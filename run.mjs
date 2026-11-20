import { readFile } from "node:fs/promises";

const [path, ...args] = process.argv.slice(2);
const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes);
const result = instance.exports.main(...args.map(Number));
console.log(result);
