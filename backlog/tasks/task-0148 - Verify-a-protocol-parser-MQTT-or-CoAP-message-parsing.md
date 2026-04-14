---
id: TASK-0148
title: 'Verify a protocol parser: MQTT or CoAP message parsing'
status: Done
assignee: []
created_date: '2026-04-10 18:46'
updated_date: '2026-04-10 20:13'
labels:
  - phase-n
  - industrial
  - security
  - real-world
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Protocol parsers are security-critical (input from untrusted network). A minimal MQTT parser (~400 LOC) or CoAP header parser. Prove: well-formed messages are parsed correctly, malformed messages are rejected (no buffer overflows), no UB on any input byte sequence. This is the 'input validation' use case that industry cares most about.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Protocol parser C source (400+ LOC)
- [ ] #2 Spec: message format as inductive type
- [ ] #3 Well-formed messages: parsed correctly (output matches spec)
- [ ] #4 Malformed messages: rejected without UB
- [ ] #5 Buffer overflow freedom proven for all inputs
- [ ] #6 No sorry
<!-- AC:END -->
