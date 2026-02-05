// jsCoq loader - exposes JsCoq to window for use by CoqService
import { JsCoq } from './jscoq.js';
window.JsCoq = JsCoq;
window.dispatchEvent(new CustomEvent('jscoq-loaded'));
