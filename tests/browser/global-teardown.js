import { removeScratch } from './scratch.js';

export default function globalTeardown() {
  removeScratch();
}
