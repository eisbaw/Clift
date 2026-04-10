---
id: TASK-0140
title: 'CImporter fuzz testing: random C programs vs gcc behavior'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
labels:
  - phase-m
  - testing
  - tcb
  - hardening
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Generate random valid C programs (using Csmith or a custom generator), run through CImporter, compile the generated Lean, and compare the CSimpl semantics against gcc execution on concrete inputs. If CSimpl says X and gcc says Y, the importer has a bug. This is adversarial testing of the TCB. seL4 tested their C parser against CompCert's parser on thousands of programs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Random C program generator (or Csmith integration) set up
- [ ] #2 Pipeline: generate C -> CImporter -> compile Lean -> extract CSimpl eval -> compare gcc output
- [ ] #3 At least 100 random programs tested
- [ ] #4 All mismatches investigated and fixed or documented
- [ ] #5 Regression tests added for each bug found
<!-- AC:END -->
