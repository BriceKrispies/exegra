import { resetScratch, workerCount } from './scratch.js';

export default function globalSetup() {
  for (let i = 0; i < workerCount(); i++) {
    resetScratch('exegra', i);
    resetScratch('multiplayer', i);
  }
}
