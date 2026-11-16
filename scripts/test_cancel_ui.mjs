// Exercise the actual upstream controller plus the Rust server's appended fix.
// Run with: node --test scripts/test_cancel_ui.mjs
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';
import vm from 'node:vm';

function controller() {
    const requests = [], dialogs = [];
    let click, resets = 0;
    const element = {
        ready() {},
        hide() { return this; },
        fadeIn() { return this; },
        stop() { resets++; return this; },
        children() { return this; },
        unbind() { click = undefined; return this; },
        click(handler) { click = handler; return this; }
    };
    const $ = () => element;
    $.ajax = request => requests.push(request);
    const context = vm.createContext({ $, document: {} });
    for (const file of [
        '../tamarin-prover/data/js/tamarin-prover-ui.js',
        '../crates/tamarin-server/src/handlers/cancel_request.js'
    ]) {
        vm.runInContext(readFileSync(new URL(file, import.meta.url), 'utf8'), context);
    }
    context.ui.showDialog = text => dialogs.push(text);
    return { context, requests, dialogs, click: () => click(), resets: () => resets };
}

test('repeated Cancel sends one request targeting the original proof', () => {
    const c = controller();
    const path = '/thy/trace/1/autoprove/foo?bound=2';
    c.context.server.performASR(path, 'json', false, () => {}, () => {});
    c.click();
    c.click();
    assert.equal(c.requests.length, 2);
    assert.equal(c.requests[1].url, '/kill?path=' + encodeURIComponent(path));
    c.requests[1].success('Cancelled');
    c.click();
    assert.equal(c.requests.length, 2);
    assert.equal(c.resets(), 1);
    assert.deepEqual(c.dialogs, ['Cancelled']);
});

test('a failed cancellation can be retried against the same proof', () => {
    const c = controller();
    c.context.loadingScreen.show('/proof');
    c.click();
    c.requests[0].error();
    c.click();
    assert.equal(c.requests.length, 2);
    assert.equal(c.requests[0].url, c.requests[1].url);
    assert.equal(c.dialogs.length, 1);
    assert.equal(c.resets(), 0);
});

for (const completion of ['success', 'error']) {
    test(`late original proof ${completion} cannot reset or update a restarted proof`, () => {
        const c = controller();
        const results = [];
        const start = name => c.context.server.performASR('/proof', 'json', false,
            data => results.push([name, data]), error => results.push([name, error]));
        start('old');
        c.click();
        c.requests[1].success('Cancelled');
        start('new');
        c.requests[0][completion]('Cancelled old proof');
        assert.equal(c.resets(), 1);
        assert.deepEqual(results, []);
        assert.deepEqual(c.dialogs, ['Cancelled']);
        c.click();
        assert.equal(c.requests[3].url, '/kill?path=%2Fproof');
        c.requests[2].success('New proof result');
        assert.deepEqual(results, [['new', 'New proof result']]);
    });

    test(`old cancellation ${completion} leaves a new request's controls intact`, () => {
        const c = controller();
        c.context.loadingScreen.show('/proof');
        c.click();
        // Reusing the same URL must still represent a new request.
        c.context.loadingScreen.show('/proof');
        c.requests[0][completion]('Old cancellation');
        assert.equal(c.resets(), 0);
        assert.deepEqual(c.dialogs, []);
        c.click();
        c.click();
        assert.equal(c.requests.length, 2);
        assert.equal(c.requests[1].url, '/kill?path=%2Fproof');
    });
}
