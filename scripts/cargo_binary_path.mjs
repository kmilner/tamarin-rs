// Read Cargo's JSON build output and print the actual executable for make install.
// Cargo can put it in a target-specific directory configured outside the Makefile.
import { createInterface } from 'node:readline';

const executables = new Set();
for await (const line of createInterface({ input: process.stdin })) {
    if (!line.trim()) continue;
    const message = JSON.parse(line);
    if (message.reason === 'compiler-artifact'
        && message.target.name === 'tamarin-rs'
        && message.target.kind.includes('bin')
        && message.executable) {
        executables.add(message.executable);
    }
}

if (executables.size !== 1) {
    console.error(`Expected one tamarin-rs executable from Cargo, got ${executables.size}`);
    process.exit(1);
}
console.log([...executables][0]);
