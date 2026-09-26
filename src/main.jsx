import React, { useEffect, useMemo, useRef, useState } from "react";
import { createRoot } from "react-dom/client";
import * as pdfjsLib from "pdfjs-dist";
import "./style.css";

pdfjsLib.GlobalWorkerOptions.workerSrc = new URL(
  "pdfjs-dist/build/pdf.worker.mjs",
  import.meta.url
).toString();

const DB_NAME = "pdf-name-search-v3";
const DB_VERSION = 1;
const STORE = "documents";

function normalize(s = "") {
  return String(s)
    .normalize("NFKC")
    .replace(/[\u200B-\u200D\uFEFF]/g, "")
    .replace(/\s+/g, " ")
    .trim()
    .toLowerCase();
}

function compact(s = "") {
  return normalize(s).replace(/[^a-z0-9]/g, "");
}

function tokenize(s = "") {
  return normalize(s).split(/\s+/).filter(Boolean);
}

function levenshtein(a, b, max = 6) {
  a = compact(a);
  b = compact(b);
  if (!a || !b) return 0;
  if (a === b) return 100;
  if (Math.abs(a.length - b.length) > max) return 0;

  let prev = Array.from({ length: b.length + 1 }, (_, i) => i);
  for (let i = 1; i <= a.length; i++) {
    const cur = [i];
    let rowMin = cur[0];
    for (let j = 1; j <= b.length; j++) {
      cur[j] = Math.min(
        cur[j - 1] + 1,
        prev[j] + 1,
        prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1)
      );
      rowMin = Math.min(rowMin, cur[j]);
    }
    if (rowMin > max) return 0;
    prev = cur;
  }
  return Math.max(
    0,
    Math.round((1 - prev[b.length] / Math.max(a.length, b.length)) * 100)
  );
}

function openDB() {
  return new Promise((resolve, reject) => {
    const req = indexedDB.open(DB_NAME, DB_VERSION);
    req.onupgradeneeded = () => {
      if (!req.result.objectStoreNames.contains(STORE)) {
        req.result.createObjectStore(STORE);
      }
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
}

async function dbGet(key) {
  const db = await openDB();
  return new Promise((resolve, reject) => {
    const tx = db.transaction(STORE, "readonly");
    const req = tx.objectStore(STORE).get(key);
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
}

async function dbPut(key, value) {
  const db = await openDB();
  return new Promise((resolve, reject) => {
    const tx = db.transaction(STORE, "readwrite");
    tx.objectStore(STORE).put(value, key);
    tx.oncomplete = resolve;
    tx.onerror = () => reject(tx.error);
  });
}

async function dbDelete(key) {
  const db = await openDB();
  return new Promise((resolve, reject) => {
    const tx = db.transaction(STORE, "readwrite");
    tx.objectStore(STORE).delete(key);
    tx.oncomplete = resolve;
    tx.onerror = () => reject(tx.error);
  });
}

async function makeFileId(file) {
  const head = new Uint8Array(
    await file.slice(0, Math.min(file.size, 262144)).arrayBuffer()
  );
  let h = 2166136261;
  for (const byte of head) {
    h ^= byte;
    h = Math.imul(h, 16777619);
  }
  return `${file.name}|${file.size}|${file.lastModified}|${(h >>> 0).toString(16)}`;
}

function getItemText(item) {
  return String(item.str || "").replace(/\s+/g, " ").trim();
}

/*
  This PDF is a tabular electoral roll. Each page contains:
  Sr No | Elector Name | Relative Name | Address | Qualification |
  Occupation | Age | Gender | Epic No | Photo

  PDF.js does not preserve HTML-like table rows. We therefore rebuild rows
  from text coordinates (x/y), then search INSIDE the matching voter row.
  This prevents details from the person immediately above/below from leaking
  into the result.
*/
function groupTextLines(items, yTolerance = 3) {
  const clean = items
    .map((item) => ({
      str: getItemText(item),
      x: Number(item.transform?.[4] || 0),
      y: Number(item.transform?.[5] || 0),
      width: Number(item.width || 0)
    }))
    .filter((x) => x.str);

  clean.sort((a, b) => b.y - a.y || a.x - b.x);

  const lines = [];
  for (const item of clean) {
    let line = lines.find((l) => Math.abs(l.y - item.y) <= yTolerance);
    if (!line) {
      line = { y: item.y, items: [] };
      lines.push(line);
    }
    line.items.push(item);
  }

  for (const line of lines) {
    line.items.sort((a, b) => a.x - b.x);
    line.text = line.items.map((x) => x.str).join(" ").replace(/\s+/g, " ").trim();
  }

  return lines.sort((a, b) => b.y - a.y);
}

function isLikelySerialLine(line, pageWidth) {
  if (!line?.items?.length) return false;
  const first = line.items[0];
  if (first.x > pageWidth * 0.14) return false;
  if (!/^\d{1,5}$/.test(first.str)) return false;
  // The column-number header is also numeric, but contains the table labels.
  if (/elector|relative|address|qualification|occupation|gender|age|epic|photo/i.test(line.text)) {
    return false;
  }
  return true;
}

function parsePartNumber(fullText) {
  const matches = [...String(fullText).matchAll(/\bpart\s*[:\-]?\s*(\d+)\b/gi)];
  return matches.length ? matches[0][1] : "—";
}

function columnForX(x, pageWidth) {
  const r = x / pageWidth;
  // Boundaries match the supplied Maharashtra electoral-roll table layout.
  if (r < 0.235) return "name";
  if (r < 0.367) return "relative";
  if (r < 0.500) return "address";
  if (r < 0.589) return "qualification";
  if (r < 0.706) return "occupation";
  if (r < 0.741) return "age";
  if (r < 0.778) return "gender";
  if (r < 0.907) return "epic";
  return "photo";
}

function cleanField(parts) {
  return parts
    .join(" ")
    .replace(/\s+/g, " ")
    .replace(/\s+([,./-])/g, "$1")
    .trim();
}

function makeRecord(lines, start, end, pageWidth, partNo) {
  const fields = {
    name: [],
    relative: [],
    address: [],
    qualification: [],
    occupation: [],
    age: [],
    gender: [],
    epic: [],
    photo: []
  };

  for (let i = start; i < end; i++) {
    for (const item of lines[i].items) {
      // The first cell of a voter row is Sr No, not part of the person's name.
      if (i === start && item === lines[i].items[0] && /^\d{1,5}$/.test(item.str)) {
        continue;
      }
      const col = columnForX(item.x, pageWidth);
      fields[col].push(item.str);
    }
  }

  const name = cleanField(fields.name);
  const address = cleanField(fields.address);
  const age = cleanField(fields.age);
  const gender = cleanField(fields.gender);

  // Ignore header/garbage rows that have no meaningful name.
  if (!name || /elector\s*name/i.test(name) || /^name$/i.test(name)) return null;

  const serial = cleanField([lines[start]?.items?.[0]?.str || ""]).match(/^\d{1,5}$/)?.[0] || "—";

  return {
    serial,
    name,
    relative: cleanField(fields.relative),
    address,
    qualification: cleanField(fields.qualification),
    occupation: cleanField(fields.occupation),
    age: age.match(/\b\d{1,3}\b/)?.[0] || age,
    gender,
    epic: cleanField(fields.epic),
    partNo,
    searchable: normalize([
      name,
      cleanField(fields.relative),
      address,
      cleanField(fields.qualification),
      cleanField(fields.occupation),
      age,
      gender,
      cleanField(fields.epic)
    ].join(" "))
  };
}

function parsePageRecords(content, pageWidth) {
  const items = content.items || [];
  const fullText = items.map((x) => x.str || "").join(" ");
  const partNo = parsePartNumber(fullText);
  const lines = groupTextLines(items);

  const starts = [];
  for (let i = 0; i < lines.length; i++) {
    if (isLikelySerialLine(lines[i], pageWidth)) starts.push(i);
  }

  const records = [];
  for (let i = 0; i < starts.length; i++) {
    const start = starts[i];
    const end = starts[i + 1] ?? lines.length;
    const record = makeRecord(lines, start, end, pageWidth, partNo);
    if (record) records.push(record);
  }

  return { partNo, records, fullText };
}

function findFuzzyRecord(records, query, threshold) {
  let best = null;
  const nq = normalize(query);
  const qWords = tokenize(query);

  for (const record of records) {
    const score = levenshtein(nq, normalize(record.name), 7);
    const tokenScore = qWords.length
      ? Math.round(
          (qWords.filter((w) => normalize(record.name).includes(w)).length /
            qWords.length) *
            100
        )
      : 0;
    const finalScore = Math.max(score, tokenScore);
    if (finalScore >= Number(threshold) && (!best || finalScore > best.score)) {
      best = { record, score: finalScore };
    }
  }
  return best;
}

function App() {
  const [file, setFile] = useState(null);
  const [fileKey, setFileKey] = useState("");
  const [index, setIndex] = useState(null);
  const [query, setQuery] = useState("");
  const [threshold, setThreshold] = useState(84);
  const [building, setBuilding] = useState(false);
  const [searching, setSearching] = useState(false);
  const [status, setStatus] = useState("Choose a PDF to begin.");
  const [processed, setProcessed] = useState(0);
  const [totalPages, setTotalPages] = useState(0);
  const [results, setResults] = useState([]);
  const [viewerPage, setViewerPage] = useState(null);
  const [viewerPdf, setViewerPdf] = useState(null);
  const [viewerScale, setViewerScale] = useState(1);
  const [url, setUrl] = useState("");
  const pdfRef = useRef(null);
  const canvasRef = useRef(null);
  const viewerHostRef = useRef(null);

  const progress = useMemo(
    () => (totalPages ? Math.round((processed / totalPages) * 100) : 0),
    [processed, totalPages]
  );

  useEffect(() => () => url && URL.revokeObjectURL(url), [url]);

  async function extractPage(pdf, pageNo) {
    const page = await pdf.getPage(pageNo);
    const content = await page.getTextContent();
    const viewport = page.getViewport({ scale: 1 });
    const parsed = parsePageRecords(content, viewport.width);
    page.cleanup();
    return { page: pageNo, ...parsed };
  }

  async function buildIndex(selectedFile, key) {
    setBuilding(true);
    setResults([]);

    try {
      const cached = await dbGet(key);
      const bytes = new Uint8Array(await selectedFile.arrayBuffer());
      const pdf = await pdfjsLib.getDocument({
        data: bytes,
        disableAutoFetch: false,
        disableStream: false
      }).promise;

      pdfRef.current = pdf;
      setTotalPages(pdf.numPages);

      if (
        cached?.version === 4 &&
        cached.numPages === pdf.numPages &&
        Array.isArray(cached.pages)
      ) {
        setIndex(cached);
        setProcessed(pdf.numPages);
        setStatus(`Index loaded — ${pdf.numPages.toLocaleString()} pages ready.`);
        return;
      }

      const pages = new Array(pdf.numPages);
      const batchSize = 8;

      for (let start = 1; start <= pdf.numPages; start += batchSize) {
        const end = Math.min(start + batchSize - 1, pdf.numPages);
        const extracted = await Promise.all(
          Array.from({ length: end - start + 1 }, (_, i) =>
            extractPage(pdf, start + i)
          )
        );

        for (const item of extracted) pages[item.page - 1] = item;
        setProcessed(end);
        setStatus(`Indexing ${end.toLocaleString()} / ${pdf.numPages.toLocaleString()} pages…`);
        await new Promise((r) => setTimeout(r, 0));
      }

      const saved = {
        version: 4,
        name: selectedFile.name,
        size: selectedFile.size,
        numPages: pdf.numPages,
        pages
      };

      setStatus("Saving fast voter-record index…");
      await dbPut(key, saved);
      setIndex(saved);
      setStatus(`Ready — ${pdf.numPages.toLocaleString()} pages indexed.`);
    } catch (error) {
      console.error(error);
      setStatus("Could not read this PDF. Image-only/scanned PDFs require OCR.");
    } finally {
      setBuilding(false);
    }
  }

  async function handleFile(event) {
    const selected = event.target.files?.[0];
    if (!selected) return;
    if (selected.type !== "application/pdf") {
      alert("Please choose a PDF file.");
      return;
    }

    if (url) URL.revokeObjectURL(url);
    setFile(selected);
    setUrl(URL.createObjectURL(selected));
    setIndex(null);
    setResults([]);
    setProcessed(0);
    setTotalPages(0);
    setStatus("Opening PDF and checking saved index…");

    const key = await makeFileId(selected);
    setFileKey(key);
    await buildIndex(selected, key);
  }

  function search() {
    if (!index) return alert("Please upload a PDF first.");
    if (!query.trim()) return alert("Enter a name to search.");

    setSearching(true);
    setResults([]);

    requestAnimationFrame(() => {
      const q = normalize(query);
      const exact = [];

      for (const page of index.pages) {
        for (const record of page.records || []) {
          if (normalize(record.name).includes(q)) {
            exact.push({
              page: page.page,
              partNo: record.partNo || page.partNo || "—",
              record,
              exact: true,
              score: 100
            });
          }
        }
      }

      if (exact.length) {
        setResults(exact);
        setStatus(`Found ${exact.length.toLocaleString()} exact person record(s).`);
        setSearching(false);
        return;
      }

      const fuzzy = [];
      for (const page of index.pages) {
        const best = findFuzzyRecord(page.records || [], query, threshold);
        if (best) {
          fuzzy.push({
            page: page.page,
            partNo: best.record.partNo || page.partNo || "—",
            record: best.record,
            exact: false,
            score: best.score
          });
        }
      }
      fuzzy.sort((a, b) => b.score - a.score || a.page - b.page);
      setResults(fuzzy);
      setStatus(
        fuzzy.length
          ? `No exact name found. Found ${fuzzy.length.toLocaleString()} possible person record(s).`
          : "No matching person found."
      );
      setSearching(false);
    });
  }

  async function renderViewerPage(pageNumber, scale = viewerScale) {
    if (!viewerPdf || !canvasRef.current) return;
    const page = await viewerPdf.getPage(pageNumber);
    const base = page.getViewport({ scale: 1 });
    const hostWidth = Math.max(280, (viewerHostRef.current?.clientWidth || 900) - 24);
    const mobileFit = Math.min(1.55, hostWidth / base.width);
    const finalScale = Math.max(0.6, mobileFit * scale);
    const viewport = page.getViewport({ scale: finalScale });

    const canvas = canvasRef.current;
    const context = canvas.getContext("2d", { alpha: false });
    canvas.width = Math.ceil(viewport.width);
    canvas.height = Math.ceil(viewport.height);
    canvas.style.width = `${Math.ceil(viewport.width)}px`;
    canvas.style.height = `${Math.ceil(viewport.height)}px`;

    await page.render({ canvasContext: context, viewport }).promise;
    if (viewerHostRef.current) viewerHostRef.current.scrollTop = 0;
  }

  function openExactPage(pageNumber) {
    if (!pdfRef.current) return;
    setViewerPdf(pdfRef.current);
    setViewerPage(pageNumber);
    setViewerScale(1);
  }

  useEffect(() => {
    if (viewerPdf && viewerPage && canvasRef.current) {
      const timer = setTimeout(() => renderViewerPage(viewerPage, viewerScale), 20);
      return () => clearTimeout(timer);
    }
  }, [viewerPdf, viewerPage, viewerScale]);

  useEffect(() => {
    if (!viewerPdf || !viewerPage) return;
    const onResize = () => renderViewerPage(viewerPage, viewerScale);
    window.addEventListener("resize", onResize);
    return () => window.removeEventListener("resize", onResize);
  }, [viewerPdf, viewerPage, viewerScale]);

  function closeViewer() {
    setViewerPage(null);
    setViewerPdf(null);
  }

  async function clearIndex() {
    if (fileKey) await dbDelete(fileKey);
    setIndex(null);
    setResults([]);
    setProcessed(0);
    setTotalPages(0);
    setStatus("Saved index cleared. Upload the PDF again to rebuild it.");
  }

  function exportCSV() {
    const rows = [
      ["Serial No", "Name", "Part No", "Age", "Address", "PDF Page", "Match"],
      ...results.map((r) => [
        r.record.serial,
        r.record.name,
        r.partNo,
        r.record.age,
        r.record.address,
        r.page,
        r.exact ? "EXACT" : `${r.score}% FUZZY`
      ])
    ];

    const csv = rows
      .map((row) => row.map((x) => `"${String(x ?? "").replace(/"/g, '""')}"`).join(","))
      .join("\n");
    const downloadUrl = URL.createObjectURL(
      new Blob([csv], { type: "text/csv;charset=utf-8" })
    );
    const a = document.createElement("a");
    a.href = downloadUrl;
    a.download = "pdf-person-search-results.csv";
    a.click();
    setTimeout(() => URL.revokeObjectURL(downloadUrl), 1000);
  }

  return (
    <div className="app">
      <header className="topbar">
        <div className="brand">PDF<span>Search</span></div>
        <div className="headerText">
          <h1>Electoral Roll Name Search</h1>
          <p>Search a person and get Serial No, Name, Part No, Age and Address from the exact record.</p>
        </div>
      </header>

      <main className="container">
        <section className="card">
          <label className={`upload ${building ? "disabled" : ""}`}>
            <input type="file" accept="application/pdf" onChange={handleFile} disabled={building} />
            <div className="uploadIcon">📄</div>
            <strong>{file ? file.name : "Choose your electoral-roll PDF"}</strong>
            <span>{file ? `${(file.size / 1048576).toFixed(1)} MB` : "Tap or click to upload"}</span>
          </label>

          {totalPages > 0 && (
            <div className="progressBox">
              <div className="progressLine">
                <span>{building ? "Building voter-record index" : "Index ready"}</span>
                <b>{progress}%</b>
              </div>
              <div className="progressBar"><div style={{ width: `${progress}%` }} /></div>
              <small>{processed.toLocaleString()} / {totalPages.toLocaleString()} pages processed</small>
            </div>
          )}

          <label className="label">Search Person Name</label>
          <div className="searchRow">
            <input
              className="searchInput"
              value={query}
              disabled={!index || searching || building}
              onChange={(e) => setQuery(e.target.value)}
              onKeyDown={(e) => e.key === "Enter" && !searching && search()}
              placeholder="Example: Tushar Raut"
            />
            <button className="searchBtn" disabled={!index || searching || building} onClick={search}>
              {searching ? "SEARCHING…" : "SEARCH"}
            </button>
          </div>

          <div className="fuzzyBox">
            <div><span>Fuzzy matching threshold</span><b>{threshold}%</b></div>
            <input type="range" min="60" max="95" value={threshold} onChange={(e) => setThreshold(e.target.value)} />
            <small>Exact name is checked first. Fuzzy matching searches voter records, not the whole page.</small>
          </div>

          <div className="status">{status}</div>
          {index && <button className="clearBtn" onClick={clearIndex}>CLEAR SAVED INDEX</button>}
        </section>

        <section className="card">
          <div className="resultHeader">
            <div>
              <h2>Person Details</h2>
              <span>{results.length.toLocaleString()} matching record(s)</span>
            </div>
            {results.length > 0 && <button className="exportBtn" onClick={exportCSV}>EXPORT CSV</button>}
          </div>

          {!results.length ? (
            <div className="empty">
              <div>🔎</div>
              <strong>No results yet</strong>
              <p>Upload the PDF, wait for indexing, then search a person's name.</p>
            </div>
          ) : (
            <div className="resultsList">
              {results.map((result, i) => (
                <article className="result" key={`${result.page}-${result.record.name}-${i}`}>
                  <div className="resultBody">
                    <div className="resultMeta">
                      <strong>Page {result.page}</strong>
                      <span className={result.exact ? "exact" : "fuzzy"}>
                        {result.exact ? "EXACT MATCH" : `${result.score}% MATCH`}
                      </span>
                    </div>

                    <div className="personGrid">
                      <div><span>Serial No</span><strong>{result.record.serial || "—"}</strong></div>
                      <div><span>Name</span><strong>{result.record.name}</strong></div>
                      <div><span>Part No</span><strong>{result.partNo}</strong></div>
                      <div><span>Age</span><strong>{result.record.age || "—"}</strong></div>
                      <div className="addressField"><span>Address</span><strong>{result.record.address || "—"}</strong></div>
                    </div>
                  </div>

                  <button className="openBtn" onClick={() => openExactPage(result.page)}>
                    VIEW EXACT PAGE
                  </button>
                </article>
              ))}
            </div>
          )}
        </section>

        <section className="features">
          <div><b>🎯 Record-level search</b><span>Neighboring voters are not included in the result.</span></div>
          <div><b>🔢 Serial No included</b><span>Serial number is taken from the voter row.</span></div>
          <div><b>📌 Part No included</b><span>Part number is read from the page header.</span></div>
          <div><b>📱 Exact page viewer</b><span>The matching PDF page opens inside the app on mobile and desktop.</span></div>
          <div><b>⚡ Fast repeat search</b><span>The structured index is saved in your browser.</span></div>
        </section>
      </main>

      {viewerPage && (
        <div className="viewerOverlay">
          <div className="viewerHeader">
            <button onClick={closeViewer}>✕ CLOSE</button>
            <strong>PDF Page {viewerPage}</strong>
            <div className="viewerControls">
              <button onClick={() => setViewerScale((s) => Math.max(0.7, s - 0.15))}>−</button>
              <span>{Math.round(viewerScale * 100)}%</span>
              <button onClick={() => setViewerScale((s) => Math.min(2, s + 0.15))}>+</button>
            </div>
          </div>
          <div className="viewerBody" ref={viewerHostRef}>
            <canvas ref={canvasRef} />
          </div>
        </div>
      )}
    </div>
  );
}

createRoot(document.getElementById("root")).render(<App />);
