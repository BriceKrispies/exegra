# Widget Service

A small service that stores widgets and serves them to browsers.

## Goals

- **G-1** Widgets are stored durably.

## Decisions

- **D-1** **One store.** All widgets live in a single database.

## Process topology

### Process topology

| ID | Component | Owns | Talks to |
|---|---|---|---|
| C-1 | Widget API | Widget requests, D-1 | C-2 |
| C-2 | Widget store | Widget state | C-1 |

## Boundaries

| ID | Boundary | Kind | Who uses it |
|---|---|---|---|
| B-1 | Widget HTTP interface | HTTP | browsers |
