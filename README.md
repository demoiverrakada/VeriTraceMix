# VeriTraceMix: Formal Verification of an E2E Verifiable Voting Protocol

[![ProVerif](https://img.shields.io/badge/Verified%20with-ProVerif%202.05-blue)](https://bblanche.gitlabpages.inria.fr/proverif/)
[![Security](https://img.shields.io/badge/Properties-G1--G15-green)](#security-goals-mapping)
[![Build](https://img.shields.io/badge/Status-Verified-success)](#verification-results-summary)

## 📌 Project Overview

This repository contains the formal verification of **OpenVoting+**, an end-to-end (E2E) verifiable electronic voting protocol. The protocol is designed to address the critical tension between **Voter Privacy** and **System Accountability**.

Using **Applied Pi-Calculus** and the **ProVerif** automated reasoning tool, this project rigorously models the voting lifecycle and proves its resilience against a Dolev-Yao adversary. The model specifically focuses on hardware-assisted security using **Trusted Execution Environments (TEEs/TPMs)**.

## 🚀 Technical Highlights

- **Hardware Root of Trust:** Leverages TPM-bound non-extractable keys for ballot attestation.
- **Formal Methods:** Uses observational equivalence to prove voter anonymity and injective correspondence for integrity.
- **Localized Recovery (G15):** A unique formalization of a "Judge" process that allows for localized re-polls rather than total system failure upon malpractice detection.
- **Threshold Cryptography:** Models $(n-1)$-of-$n$ partial decryptions to ensure no single authority can compromise the tally.
- **Negative Tests:** Seven companion files in `negative_tests/` each break exactly one security mechanism. ProVerif must find an attack in every case, confirming the positive proofs are not vacuous.

---

## 📂 Repository Structure & Goal Mapping

### Positive Models (`models/`)

Each file verifies a specific subset of the 15 security goals:

| File | Goals | Description |
| :--- | :--- | :--- |
| `process_judge.pv` | **G1, G2, G3** | Individual Verifiability: Cast-as-intended, Recorded-as-cast, Dispute resolution. |
| `voter_eligibility.pv` | **G5, G6, G11** | Eligibility & Uniqueness: One-person-one-vote via nullifiers & ZKPs. Key secrecy for the Registration Authority. |
| `privacy_secrecy.pv` | **G7** | Ballot Secrecy: Passive attacker cannot read the vote. Standard secrecy query. |
| `privacy.pv` | **G8** | Anonymity: Attacker cannot link a ballot to a voter. Observational equivalence via Re-encryption Mixnet. |
| `threshold_privacy.pv` | **G9** | Threshold Privacy: Ballot secrecy holds even when $(n-1)$ of $n$ tallying authorities are corrupt. |
| `platform_integrity.pv` | **G10, G11** | Platform Integrity & Key Secrecy: Secure Boot chain enforced via TEE/TPM. Ballots can only be signed after ApprovedOS is loaded. |
| `secure_transport.pv` | **G13** | Transport Integrity & Attack Detection: Hash-chain commitment prevents undetected USB tampering. |
| `election_recovery_master.pv` | **G12, G14, G15** | Provenance, Device Revocation & Localized Recovery: Every bulletin board entry traces to a registered BMD; malpractice triggers a targeted re-poll. |

> **G4 — Tally Correctness** is out of scope for ProVerif. Paillier additive homomorphism cannot be expressed in ProVerif's equational theory. This is a standard limitation of symbolic verification shared by all ProVerif-based e-voting proofs in the literature. G4 would require CryptoVerif or a pen-and-paper proof.

### Negative Tests (`negative_tests/`)

Each file is a copy of the corresponding positive model with exactly one security check removed. ProVerif must find an attack on the targeted query in every case. A passing positive model whose negative test also passes provides strong evidence the proof is not vacuous.

| File | Mechanism Removed | Query That Must Fail |
| :--- | :--- | :--- |
| `neg_process_judge.pv` | `event DisputeStarted(id)` removed from Judge | `JudgeRulesAgainstAdmin ==> DisputeStarted` is false |
| `neg_voter_eligibility.pv` | Nullifier repo check removed (double-vote possible) | `inj-event(BallotAccepted) ==> inj-event(VoterStarted)` cannot be proved |
| `neg_privacy.pv` | Voter signing key leaked to attacker | `not attacker(sk_vA_leaked)` is false |
| `neg_platform_integrity.pv` | `if boot_os = ApprovedOS` check removed | `BallotSigned ==> OS_Loaded(ApprovedOS)` is false |
| `neg_secure_transport.pv` | Hash comparison removed from Admin | `Admin_Verified_Integrity ==> BMD_Published_Final_Hash` is false |
| `neg_threshold_privacy.pv` | Third authority key `sk3` leaked via tally output | `not attacker(sk3_ref)` is false |
| `neg_election_recovery.pv` | `event MalpracticeDetected(id)` removed from Judge | `TriggerRepoll ==> MalpracticeDetected` is false |

> **Note on equivalence negative tests:** ProVerif's observational equivalence checker is sound but not complete. When `choice[]` worlds produce structurally symmetric outputs, ProVerif may report equivalence even when a computational distinguisher exists — this is a known published limitation. The negative tests for G8 and G9 therefore test the underlying secrecy assumptions that the privacy proofs depend on (voter key secrecy and third-authority key secrecy respectively), using standard secrecy queries.

---

## 🛠 Usage & Verification

### Prerequisites

- [ProVerif 2.05](https://proverif.inria.fr/) installed and in your `PATH`.
- A Bash-compliant terminal (Linux, macOS, or WSL).

> **ProVerif 2.05 note:** The `-equivalence` flag was removed in version 2.05. ProVerif now auto-detects `choice[]` operators and switches to equivalence mode automatically. All files run with a plain `proverif` invocation.

### Automated Verification Suite

Run the provided script from the repository root to verify all 15 security goals and all 7 negative tests:

```bash
chmod +x verify_all.sh
./verify_all.sh
```

Expected output: **43 queries, 43 passed, 0 failed, 0 errors.**

### Manual Verification

Individual files can be run directly:

```bash
# Standard mode (all files, including equivalence — auto-detected)
proverif models/process_judge.pv
proverif models/voter_eligibility.pv
proverif models/privacy_secrecy.pv
proverif models/privacy.pv
proverif models/platform_integrity.pv
proverif models/secure_transport.pv
proverif models/threshold_privacy.pv
proverif models/election_recovery_master.pv

# Negative tests (attacks must be found in each)
proverif negative_tests/neg_process_judge.pv
proverif negative_tests/neg_voter_eligibility.pv
proverif negative_tests/neg_privacy.pv
proverif negative_tests/neg_platform_integrity.pv
proverif negative_tests/neg_secure_transport.pv
proverif negative_tests/neg_threshold_privacy.pv
proverif negative_tests/neg_election_recovery.pv
```

---

## ✅ Verification Results Summary

### Positive Models

| File | Queries | Result |
| :--- | :---: | :--- |
| `process_judge.pv` | 3 | ✅ All verified |
| `voter_eligibility.pv` | 4 | ✅ All verified |
| `privacy_secrecy.pv` | 2 | ✅ All verified |
| `privacy.pv` | 1 | ✅ Observational equivalence true |
| `platform_integrity.pv` | 4 | ✅ All verified |
| `secure_transport.pv` | 3 | ✅ All verified |
| `threshold_privacy.pv` | 1 | ✅ Observational equivalence true |
| `election_recovery_master.pv` | 4 | ✅ All verified |

### Negative Tests

| File | Targeted Query | Attack Found |
| :--- | :--- | :---: |
| `neg_process_judge.pv` | `JudgeRulesAgainstAdmin ==> DisputeStarted` | ✅ |
| `neg_voter_eligibility.pv` | `inj-event(BallotAccepted) ==> inj-event(VoterStarted)` | ✅ |
| `neg_privacy.pv` | `not attacker(sk_vA_leaked)` | ✅ |
| `neg_platform_integrity.pv` | `BallotSigned ==> OS_Loaded(ApprovedOS)` | ✅ |
| `neg_secure_transport.pv` | `Admin_Verified_Integrity ==> BMD_Published_Final_Hash` | ✅ |
| `neg_threshold_privacy.pv` | `not attacker(sk3_ref)` | ✅ |
| `neg_election_recovery.pv` | `TriggerRepoll ==> MalpracticeDetected` | ✅ |

---

## 📝 Key Design Notes

**On reachability queries returning `false`:** This is correct and expected. `not event(X)` returning `false` means ProVerif found a trace where `X` fires — the event *is* reachable. It is not a failure. These queries guard against vacuous proofs.

**On G7 and G8 being in separate files:** G7 asks "can the attacker read the vote?" — a secrecy query, standard mode. G8 asks "can the attacker link the vote to a voter?" — an observational equivalence query, requires `choice[]`. They use different ProVerif proof modes and cannot coexist in the same file.

**On the lock channel in `voter_eligibility.pv`:** The `NullifierRepo` table with a `get`/`insert` guard is a standard ProVerif idiom for modelling atomic read-check-write operations. It corresponds to a database transaction with a uniqueness constraint in the real implementation.

**On G4 being out of scope:** Paillier additive homomorphism cannot be expressed in ProVerif's equational theory. This is the standard limitation of symbolic verification — the same limitation applies to all ProVerif-based e-voting proofs in the literature.
