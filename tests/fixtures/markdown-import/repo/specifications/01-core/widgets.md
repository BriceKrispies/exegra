# Widgets

## Storage

**WID-001** The widget store SHALL return a stored widget unchanged.
- Verify: example
- Boundary: B-1 widget reads, called by C-1
- Traces: G-1, D-1
- Milestone: 1

**WID-002** The widget API SHALL reject a widget with no name.
- Verify: example
- Traces: G-1
- Depends: WID-001
