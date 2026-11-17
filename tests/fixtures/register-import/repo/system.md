# Widget Platform: System Specification

| Item | Value |
|---|---|
| Status | Draft |

## 1. Components

| Component | Repository | Function | Team |
|---|---|---|---|
| API | `org/api` | Serves requests. | Core |
| Store | `org/store` | Keeps widgets. | Core |

Each row above is a component. See CAP-01 and conflict C-001.

## 2. Capabilities

| ID | Capability | Owner | Source |
|---|---|---|---|
| CAP-01 | Create widgets | API | [REPO:api/create.ts:1-20] |
| CAP-02 | Keep \| list widgets | Store, API | Section 1 |

### 2.1 Interfaces

| # | From | To | Interface | State |
|---|---|---|---|---|
| I-1 | API | Store | SQL over TLS | Built |
| I-2 | Browser | API | HTTPS | Planned |

## 3. Conflicts

| ID | Topic | Trusted |
|---|---|---|
| C-001 | Who owns CAP-02 | Open |

```
| Not | a table |
|---|---|
```

| Odd | Table |
|:--|--:|
| a | b |
| only one cell |

## 4. Tickets for CAP-02

| Initiative | Epic key | Summary | Source |
|---|---|---|---|
| ERQ-1 (Active) Things | ERQ-2 | [Widget] Make things | [REPO:t.md] |
| ERQ-3 (Active) Others | (no Epics) | | |

# Appendix M. By source

Packet constraint C-001 is not conflict C-001; see `[not-a-citation]` and [REPO:b `c.ts`].
