// Shared JSDoc type definitions for the semantic core. No runtime content.
export {};

/**
 * A source location inside the specification text. `file` names the product file of a layered
 * specification (src/core/layers.js) the location is in; without it the location is in the
 * specification text itself.
 * @typedef {{offset:number, length:number, line:number, column:number, file?:string}} Loc
 */

/**
 * @typedef {Object} Diagnostic
 * @property {string} code      stable machine code, e.g. "ref.unresolved"
 * @property {'error'|'warning'|'info'} severity
 * @property {string} message
 * @property {Loc} [loc]
 * @property {(string|number)[]} [path]  JSON path in the source
 * @property {string} [entityId]
 */

/**
 * One semantic entity. `data` is the plain JSON value of its declaration
 * (references are id strings). Nested entities (ports, states, transitions)
 * are entities of their own with `owner` set, and also appear raw inside
 * their owner's `data`.
 * @typedef {Object} Entity
 * @property {string} id
 * @property {string} kind   system | component | port | relationship | contract | event | behavior | state | transition | fault | scenario | assumption | claim | evidence | view
 * @property {any} data
 * @property {string|null} owner
 * @property {(string|number)[]} path
 * @property {Loc} loc
 */

/**
 * A reference from one entity to another, found at `path` in the source.
 * @typedef {{from:string, path:(string|number)[], target:string, allowed:string[], loc:Loc}} Ref
 */

/**
 * The canonical semantic model: an immutable snapshot derived from source text.
 * @typedef {Object} Model
 * @property {string} schemaVersion
 * @property {Entity} system
 * @property {Map<string, Entity>} entities   every entity by id, in declaration order
 * @property {Record<string, Entity[]>} byKind
 * @property {Ref[]} refs
 * @property {{owner:string, path:(string|number)[], src:string, loc:Loc}[]} exprs  every expression string and where it lives
 * @property {any} meta        effective meta-model: {entities, categories, relationshipKinds, projections, sections}
 * @property {any} vocabulary  raw `vocabulary` section
 * @property {string} [semanticHash]  the semantic hash, computed by the Lean kernel with the model (src/core/hash.js)
 */

/**
 * A model mutation. `type` selects an entry of OPERATIONS in operations.js.
 * @typedef {{type:string, [key:string]:any}} Operation
 */

/**
 * @typedef {Object} TransactionResult
 * @property {boolean} ok
 * @property {string} [code]             failure code when !ok
 * @property {string} [message]
 * @property {Diagnostic[]} diagnostics  diagnostics of the resulting (or rejected) state
 * @property {number} revision           revision after the call
 * @property {string} semanticHash
 * @property {string[]} affected         entity ids touched
 * @property {boolean} semanticChanged
 */

/**
 * Scene description produced by a projection (src/core/projections.js) and
 * consumed by the renderer. Purely derived; never authoritative.
 * @typedef {Object} SceneModel
 * @property {string} viewId
 * @property {string} projection
 * @property {SceneNode[]} nodes
 * @property {SceneEdge[]} edges
 * @property {{id:string, label:string, shape?:string, line?:string, color:string, kind:'node'|'edge'|'mark', mark?:string}[]} legend
 * @property {string[]} notes   statements about what the view does and does not show
 * @property {{hierarchy: string, blocks: string[], expanded?: string[], cut?: string|null, coarsen?: string[]|'all'|null}} [abstraction]  the cut a
 *   structural scene draws the derived model of (src/core/abstraction.js); its edges are that model's interactions after the view's filters;
 *   `expanded` the elements the cut opens, `cut` the declared cut with exactly these blocks, if any
 * @property {{hidden: string[], removedBlocks: string[], droppedInteractions: number, droppedWitnesses: number, pathSummaries: number,
 *   pathsThroughFiltered: number}} [filterReport]  what a structural view's filter and the viewer's hiding removed, all of it counted in the notes
 * @property {{claimId: string, status: string, expressible: boolean, explanation: string, drawn: string[], notDrawn: string[]}[]} [levelClaims]
 *   the claims stated at a cut, evaluated at the cut this scene draws, with which of their counterexample blocks and edges are drawn
 */

/**
 * @typedef {Object} SceneNode
 * @property {string} id         scene id; equals the entity id it represents
 * @property {string} entityId
 * @property {string} entityKind
 * @property {string} label
 * @property {string} [sublabel]
 * @property {string} shape      box|chamfer|cylinder|tablet|octa|hex|pipe|sphere|diamond|capsule|container
 * @property {string} color      color role name from the meta-model palette
 * @property {string|null} parent  scene id of the enclosing container node
 * @property {boolean} container   true when the node encloses children in this scene
 * @property {boolean} [collapsed] container whose children are hidden
 * @property {string} [status]     verified|supported|violated|inconclusive|not-evaluated|active|visited
 * @property {boolean} [dimmed]
 * @property {string[]} [badges]
 * @property {{kind: string, text: string, title?: string}[]} [marks]  what is known or missing about a structural block (knowledge
 *   status, planned, unstated purpose, interface disagreement), drawn as badges distinct by kind and given in text
 * @property {string} [element]    the element a structural node draws (a module element's id differs from its entityId)
 * @property {string} [elementKind]
 * @property {boolean} [block]     a block of the scene's cut (or an implicit block), not only a container of blocks
 * @property {'transparent'|'opaque'|'unknown'} [knowledge]
 */

/**
 * @typedef {Object} SceneEdge
 * @property {string} id
 * @property {string} entityId   entity the edge represents (relationship, transition, ...)
 * @property {string} entityKind
 * @property {string} from       scene node id
 * @property {string} to         scene node id
 * @property {string} line       solid|dashed|dotted
 * @property {string} color
 * @property {string} [label]
 * @property {boolean} [lifted]  edge was re-targeted to a collapsed ancestor
 * @property {string} [kind]       the (derived) interaction kind a structural edge draws
 * @property {string[]} [witnesses]  every relationship a structural edge stands for, sorted by id (the derived interaction's
 *   witnesses kept by the view's filters); entityId is the first of them in declaration order
 * @property {'static'|'runtime'|'none'} [dependencyClass]  dependency class of the relationship's kind; layout follows only static and runtime edges
 * @property {string} [key]        the derived interaction a structural edge draws (from->to:kind)
 * @property {{via: string[], kinds: string[]}} [pathSummary]  a derived path summary through removed blocks, not an interaction
 * @property {{kind: string, text: string, title?: string}[]} [marks]  what is incomplete about a drawn fact (unwitnessed, kind not
 *   coarsening, not only declared)
 * @property {string} [status]
 * @property {boolean} [dimmed]
 */

/**
 * Positions computed by layout: scene node id -> rectangle on the ground plane.
 * x/z are the centre; w/d the footprint; level is nesting depth.
 * @typedef {Record<string, {x:number, z:number, w:number, d:number, level:number}>} Placement
 */
