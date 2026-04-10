---
id: TASK-0188
title: Add BSD LICENSE and ATTRIBUTION.md to repository root
status: Done
assignee: []
created_date: '2026-04-10 20:29'
updated_date: '2026-04-10 23:39'
labels:
  - housekeeping
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The project has thorough inline attribution (ext/README.md lists all AutoCorres2 original authors, every Lean file has -- Reference: comments), but no root-level LICENSE or ATTRIBUTION file. AutoCorres2 is BSD-licensed for code and CC-BY-SA-4.0 for docs. Add a BSD license for Clift itself and an ATTRIBUTION.md crediting the AutoCorres2/seL4/Simpl lineage.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 BSD LICENSE file at repo root for Clift
- [ ] #2 ATTRIBUTION.md crediting AutoCorres2 authors (Greenaway, Lim, Klein, Hölzl, Immler, Schirmer, Sickert-Zehnter, Wimmer), Simpl (Schirmer), seL4 (Klein et al), and referencing ext/AutoCorres2/README.md for full details
- [ ] #3 Note AutoCorres2 license terms (BSD code, CC-BY-SA-4.0 docs) in ATTRIBUTION.md
<!-- AC:END -->
