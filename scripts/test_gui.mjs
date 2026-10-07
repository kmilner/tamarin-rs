// Browser regression for a standalone binary, launched outside the checkout.
// See TESTING.md for dependencies and invocation.
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import { copyFile, mkdir, mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { setTimeout as delay } from 'node:timers/promises';
import { fileURLToPath } from 'node:url';
import { chromium } from '../target/gui-browser-test/node_modules/playwright/index.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const temp = await mkdtemp(join(tmpdir(), 'tamarin-gui-'));
let server;
let browser;
let output = '';
try {
    const prefix = join(temp, 'install');
    const bin = join(prefix, 'bin/tamarin-rs');
    const theories = join(temp, 'theories');
    await mkdir(dirname(bin), { recursive: true });
    await mkdir(join(theories, 'data'), { recursive: true });
    await copyFile(resolve(process.env.RS_PATH || join(root, 'target/ci/tamarin-rs')), bin);
    await copyFile(join(root, 'crates/tamarin-server/tests/fixtures/issue193.spthy'), join(theories, 'example.spthy'));
    // A misleading data/ directory must not override the embedded GUI.
    await mkdir(join(theories, 'data/js'), { recursive: true });
    await writeFile(join(theories, 'data/js/jquery.js'), 'throw Error("wrong assets");');
    server = spawn(bin, ['interactive', '--port=0', '.'], { cwd: theories });
    server.stdout.on('data', data => { output += data; });
    server.stderr.on('data', data => { output += data; });
    server.on('error', error => { output += error; });
    let base;
    for (let attempt = 0; attempt < 300; attempt++) {
        base = output.match(/server ready at\s+(http:\/\/\S+)/)?.[1];
        if (base) break;
        assert.equal(server.exitCode, null, output);
        await delay(100);
    }
    assert.ok(base, `Server did not become ready:\n${output}`);
    assert.ok((await (await fetch(`${base}/static/js/jquery.js`)).text()).includes('jQuery'));

    browser = await chromium.launch({ executablePath: process.env.CHROMIUM_PATH, headless: true });
    const page = await browser.newPage();
    const errors = [];
    page.on('pageerror', error => errors.push(String(error)));
    page.on('console', message => {
        if (message.type() === 'error') errors.push(message.text());
    });
    page.on('response', response => {
        if (response.status() >= 400) errors.push(`${response.status()} ${response.url()}`);
    });
    page.on('requestfailed', request => errors.push(`${request.url()}: ${request.failure()?.errorText}`));
    await page.goto(base);
    await page.locator('a[href*="/overview/"]').first().waitFor();
    const proof = await (await fetch(`${base}/thy/trace/1/autoprove/idfs/0/False/proof/debug`)).json();
    assert.ok(proof.redirect, JSON.stringify(proof));
    await page.goto(base + proof.redirect);
    const graph = page.frameLocator('iframe').first().locator('dot-graph-viz svg g.node').first();
    await graph.waitFor({ state: 'visible' });

    const svg = await fetch(base + proof.redirect.replace('/overview/', '/graph/'));
    assert.equal(svg.status, 200);
    assert.match(svg.headers.get('content-type'), /image\/svg\+xml/);
    assert.match(await svg.text(), /<svg/);

    await page.goto(base + proof.redirect.replace('/overview/', '/intdot/'));
    await page.locator('dot-graph-viz svg g.node').first().waitFor({ state: 'visible' });
    assert.deepEqual(errors, [], 'Browser errors');
    console.log('GUI smoke test passed: standalone binary, page load, embedded and standalone graphs, SVG.');
} catch (error) {
    console.error(output);
    throw error;
} finally {
    if (browser) await browser.close();
    if (server && server.exitCode === null && server.pid) {
        const exited = once(server, 'exit');
        server.kill('SIGTERM');
        const timeout = setTimeout(() => server.kill('SIGKILL'), 5000);
        await exited;
        clearTimeout(timeout);
    }
    await rm(temp, { recursive: true, force: true });
}
