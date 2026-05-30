/**
 * CARDTRADELIB v63 Google Sheet license server.
 *
 * Usage:
 * 1. Create a Google Sheet.
 * 2. Extensions -> Apps Script.
 * 3. Paste this file as Code.gs.
 * 4. Run setupLicenseSheet() once and authorize.
 * 5. Deploy -> New deployment -> Web app.
 *    Execute as: Me
 *    Who has access: Anyone
 * 6. Put the /exec Web App URL into v63's 啟用/關於 tab.
 */

const PRODUCT_APP_ID = 'CARDTRADELIB';
const SHEET_NAME = 'licenses';
const HEADERS = [
  'license_id',
  'license_key_hash',
  'license_type',
  'days',
  'customer',
  'status',
  'machine_id_hash',
  'activated_at',
  'expires_at',
  'last_verified_at',
  'note',
  'created_at',
];

// If this script is not bound to a spreadsheet, put your Sheet ID here.
const SPREADSHEET_ID = '';

function doGet(e) {
  return json_({
    ok: true,
    service: 'cardtradelib-google-sheet-license',
    product: PRODUCT_APP_ID,
    message: 'Google Sheet license server is running.',
    server_time: nowIso_(),
  });
}

function doPost(e) {
  const lock = LockService.getScriptLock();
  try {
    lock.waitLock(10000);
    const payload = parsePayload_(e);
    const action = getAction_(e, payload);

    if (action === 'activate') {
      return json_(activateLicense_(payload));
    }
    if (action === 'verify') {
      return json_(verifyLicense_(payload));
    }
    if (action === 'health') {
      return doGet(e);
    }
    return json_({ ok: false, message: 'Unknown action: ' + action });
  } catch (err) {
    return json_({ ok: false, message: String(err && err.message ? err.message : err) });
  } finally {
    try { lock.releaseLock(); } catch (err) {}
  }
}

function setupLicenseSheet() {
  const sheet = getLicenseSheet_();
  const map = ensureHeaders_(sheet);
  sheet.setFrozenRows(1);
  sheet.autoResizeColumns(1, HEADERS.length);
  return map;
}

function parsePayload_(e) {
  const text = e && e.postData && e.postData.contents ? String(e.postData.contents) : '';
  if (!text) return {};
  try {
    const data = JSON.parse(text);
    return data && typeof data === 'object' ? data : {};
  } catch (err) {
    return {};
  }
}

function getAction_(e, payload) {
  if (e && e.parameter && e.parameter.action) {
    return String(e.parameter.action).replace(/^\/+/, '').toLowerCase();
  }
  if (e && e.pathInfo) {
    return String(e.pathInfo).split('/')[0].replace(/^\/+/, '').toLowerCase();
  }
  if (payload && payload.action) {
    return String(payload.action).replace(/^\/+/, '').toLowerCase();
  }
  return '';
}

function getSpreadsheet_() {
  if (SPREADSHEET_ID) {
    return SpreadsheetApp.openById(SPREADSHEET_ID);
  }
  const ss = SpreadsheetApp.getActiveSpreadsheet();
  if (!ss) {
    throw new Error('找不到 Google Sheet。請把 Apps Script 建在 Google Sheet 內，或填入 SPREADSHEET_ID。');
  }
  return ss;
}

function getLicenseSheet_() {
  const ss = getSpreadsheet_();
  let sheet = ss.getSheetByName(SHEET_NAME);
  if (!sheet) sheet = ss.insertSheet(SHEET_NAME);
  ensureHeaders_(sheet);
  return sheet;
}

function ensureHeaders_(sheet) {
  const width = Math.max(sheet.getLastColumn(), HEADERS.length);
  if (sheet.getLastRow() === 0) {
    sheet.getRange(1, 1, 1, HEADERS.length).setValues([HEADERS]);
  } else {
    const firstRow = sheet.getRange(1, 1, 1, width).getValues()[0];
    const hasAnyHeader = firstRow.some(v => String(v || '').trim());
    if (!hasAnyHeader) {
      sheet.getRange(1, 1, 1, HEADERS.length).setValues([HEADERS]);
    }
  }

  let headers = sheet.getRange(1, 1, 1, Math.max(sheet.getLastColumn(), HEADERS.length)).getValues()[0]
    .map(v => String(v || '').trim());
  for (const name of HEADERS) {
    if (headers.indexOf(name) < 0) {
      const col = headers.length + 1;
      sheet.getRange(1, col).setValue(name);
      headers.push(name);
    }
  }

  const map = {};
  headers.forEach((name, index) => {
    if (name) map[name] = index + 1;
  });
  return map;
}

function findLicense_(sheet, map, licenseId, keyHash) {
  const lastRow = sheet.getLastRow();
  const lastCol = sheet.getLastColumn();
  if (lastRow < 2) return null;
  const rows = sheet.getRange(2, 1, lastRow - 1, lastCol).getValues();
  let idOnlyMatch = null;
  for (let i = 0; i < rows.length; i++) {
    const row = rows[i];
    const rowLicenseId = cell_(row, map, 'license_id');
    const rowKeyHash = cell_(row, map, 'license_key_hash');
    if (rowLicenseId === licenseId) {
      if (rowKeyHash === keyHash) {
        return { rowIndex: i + 2, row: row, hashMismatch: false };
      }
      if (!idOnlyMatch) {
        idOnlyMatch = { rowIndex: i + 2, row: row, hashMismatch: true };
      }
    }
  }
  return idOnlyMatch;
}

function activateLicense_(payload) {
  validatePayload_(payload);
  const sheet = getLicenseSheet_();
  const map = ensureHeaders_(sheet);
  const found = findLicense_(sheet, map, payload.license_id, payload.license_key_hash);
  if (!found) {
    return fail_('Google Sheet 找不到此授權碼。請先用金鑰產生器複製 Sheet 列，貼到 licenses 工作表第 2 列以下。');
  }
  if (found.hashMismatch) {
    return fail_('授權碼 hash 不符合 Google Sheet 紀錄。請確認貼到 Sheet 的授權列是否與使用者輸入的金鑰相同。');
  }

  const row = found.row;
  const now = new Date();
  const nowIso = nowIso_(now);
  const status = cell_(row, map, 'status').toLowerCase() || 'unused';
  if (status === 'disabled') return fail_('此授權碼已停用。');

  const existingMachine = cell_(row, map, 'machine_id_hash');
  if (existingMachine && existingMachine !== payload.machine_id_hash) {
    return fail_('此授權碼已綁定其他電腦。');
  }

  const licenseType = cell_(row, map, 'license_type').toLowerCase() || 'trial';
  const days = Number(cell_(row, map, 'days')) || (licenseType === 'pro' ? 30 : 7);
  let activatedAt = parseDate_(cell_(row, map, 'activated_at'));
  let expiresAt = parseDate_(cell_(row, map, 'expires_at'));

  if (!activatedAt) {
    activatedAt = now;
    expiresAt = addDays_(activatedAt, days);
  } else if (!expiresAt) {
    expiresAt = addDays_(activatedAt, days);
  }

  if (now.getTime() > expiresAt.getTime()) {
    writeCell_(sheet, found.rowIndex, map, 'status', 'expired');
    writeCell_(sheet, found.rowIndex, map, 'last_verified_at', nowIso);
    return fail_('此授權碼已過期。');
  }

  writeCell_(sheet, found.rowIndex, map, 'status', 'active');
  writeCell_(sheet, found.rowIndex, map, 'machine_id_hash', payload.machine_id_hash);
  writeCell_(sheet, found.rowIndex, map, 'activated_at', nowIso_(activatedAt));
  writeCell_(sheet, found.rowIndex, map, 'expires_at', nowIso_(expiresAt));
  writeCell_(sheet, found.rowIndex, map, 'last_verified_at', nowIso);

  return {
    ok: true,
    message: '啟用成功。',
    status: 'active',
    activated_at: nowIso_(activatedAt),
    expires_at: nowIso_(expiresAt),
    server_time: nowIso,
  };
}

function verifyLicense_(payload) {
  validatePayload_(payload);
  const sheet = getLicenseSheet_();
  const map = ensureHeaders_(sheet);
  const found = findLicense_(sheet, map, payload.license_id, payload.license_key_hash);
  if (!found) return fail_('Google Sheet 找不到此授權碼。');
  if (found.hashMismatch) return fail_('授權碼 hash 不符合 Google Sheet 紀錄。');

  const row = found.row;
  const now = new Date();
  const nowIso = nowIso_(now);
  const status = cell_(row, map, 'status').toLowerCase() || 'unused';
  if (status === 'disabled') return fail_('此授權碼已停用。');

  const machine = cell_(row, map, 'machine_id_hash');
  if (!machine) return fail_('此授權碼尚未啟用。');
  if (machine !== payload.machine_id_hash) return fail_('此授權碼已綁定其他電腦。');

  const expiresAt = parseDate_(cell_(row, map, 'expires_at'));
  if (!expiresAt) return fail_('Google Sheet 缺少 expires_at 到期時間。');

  if (now.getTime() > expiresAt.getTime()) {
    writeCell_(sheet, found.rowIndex, map, 'status', 'expired');
    writeCell_(sheet, found.rowIndex, map, 'last_verified_at', nowIso);
    return fail_('此授權碼已過期。');
  }

  writeCell_(sheet, found.rowIndex, map, 'status', 'active');
  writeCell_(sheet, found.rowIndex, map, 'last_verified_at', nowIso);

  return {
    ok: true,
    message: '授權驗證成功。',
    status: 'active',
    activated_at: nowIso_(parseDate_(cell_(row, map, 'activated_at'))),
    expires_at: nowIso_(expiresAt),
    server_time: nowIso,
  };
}

function validatePayload_(payload) {
  if (!payload || typeof payload !== 'object') throw new Error('缺少 JSON payload。');
  if (payload.app_id !== PRODUCT_APP_ID) throw new Error('app_id 不正確。');
  if (!payload.license_id) throw new Error('缺少 license_id。');
  if (!payload.license_key_hash) throw new Error('缺少 license_key_hash。');
  if (!payload.machine_id_hash) throw new Error('缺少 machine_id_hash。');
}

function cell_(row, map, name) {
  const col = map[name];
  if (!col) return '';
  const value = row[col - 1];
  if (value instanceof Date) return nowIso_(value);
  return String(value == null ? '' : value).trim();
}

function writeCell_(sheet, rowIndex, map, name, value) {
  const col = map[name];
  if (!col) throw new Error('缺少欄位：' + name);
  sheet.getRange(rowIndex, col).setValue(value);
}

function parseDate_(value) {
  if (!value) return null;
  if (value instanceof Date) return value;
  const d = new Date(String(value));
  if (isNaN(d.getTime())) return null;
  return d;
}

function addDays_(date, days) {
  return new Date(date.getTime() + Number(days || 0) * 24 * 60 * 60 * 1000);
}

function nowIso_(date) {
  const d = date || new Date();
  return d.toISOString().replace(/\.\d{3}Z$/, 'Z');
}

function fail_(message) {
  return { ok: false, message: message, server_time: nowIso_() };
}

function json_(obj) {
  return ContentService
    .createTextOutput(JSON.stringify(obj))
    .setMimeType(ContentService.MimeType.JSON);
}
