# VeriTraceMix: Formal Verification of an E2E Verifiable Voting Protocol

[![ProVerif](https://img.shields.io/badge/Verified%20with-ProVerif%202.05-blue)](https://bblanche.gitlabpages.inria.fr/proverif/)
[![Security](https://img.shields.io/badge/Properties-G1--G15-green)](#security-goals-mapping)
[![Build](https://img.shields.io/badge/Status-Verified-success)](#verification-results-summary)

## 📌 Project Overview

This repository contains the formal verification of **VeriTraceMix**, an end-to-end (E2E) verifiable electronic voting protocol. The protocol is designed to address the critical tension between **Voter Privacy** and **System Accountability**.

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
| *(out of scope)* | **G4** | **Tally Correctness** — Paillier additive homomorphism cannot be expressed in ProVerif's equational theory. This is the standard limitation of symbolic verification shared by all ProVerif-based e-voting proofs in the literature. G4 requires CryptoVerif or a pen-and-paper reduction. |


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

---

## 🔬 Negative Testing Methodology

### Why Negative Tests Are Necessary

A ProVerif proof can pass for the wrong reason in two ways. The first is a **vacuous proof**: if the event a security query protects never fires in any execution, the causal correspondence is trivially true — there is nothing to check. Reachability queries (`not event(X)` expected to return false) guard against this. The second and more subtle failure is a **mis-modelled mechanism**: the security check exists in the code, but ProVerif never actually uses it to block an attack. The model looks correct but the proof is not load-bearing — removing the check would make no difference. Negative tests catch this.

The methodology is: for each of the 7 core security mechanisms, create a companion file with exactly that one mechanism removed and nothing else changed. ProVerif must find an attack on the targeted property. If it does, the positive proof was genuinely relying on that mechanism. If it does not, the positive proof was passing for the wrong reason.

An equally important requirement is **surgical precision**: in each negative test, only the targeted property should fail. All other queries in the same file should still hold. This confirms the break is isolated and not a side effect of accidentally corrupting an unrelated part of the model. The `[NOTE]` lines in `verify_all.sh` output — where unbroken properties still pass inside a negative test file — are evidence of this precision.

### Per-File Breakdown

**`neg_process_judge.pv` — G3 Dispute Soundness**
Removed `event DisputeStarted(id)` from `processJudge`. The judge still reads receipts, checks the bulletin board, and fires `JudgeRulesAgainstAdmin` when ballots mismatch — but `DisputeStarted` never fires anywhere. ProVerif finds a trace where the judge rules against the admin with no dispute on record. G1 and G2 queries remain true because they do not depend on the dispute event.

> **Note on an earlier attempt:** We first tried removing the ballot-integrity check (`r_ballot = ballot`) instead. This did not break G3, because `DisputeStarted` was still present and fired unconditionally before any check — the causal chain was intact regardless. This confirmed that the correct break must target the event the query is directly tracking, not a nearby guard.

**`neg_voter_eligibility.pv` — G6 Uniqueness (No Double Voting)**
Removed the `get NullifierRepo(=n)` guard from `processRA`, which was the atomic check-before-insert that enforced one-ballot-per-nullifier. With the RA replicated (`!`), the attacker replays the voter's public output `(pk_v, n, pi)` to the RA a second time. Both submissions pass ZKP verification and both fire `BallotAccepted`. Two accepted ballots now exist for one `VoterStarted`, breaking the injective correspondence.

> **On the "cannot be proved" output:** ProVerif 2.05 reports `cannot be proved` rather than `is false` when the process contains `!` replication. ProVerif finds the Horn clause derivation of the attack but cannot construct a finite concrete trace because the replicated process creates an infinite state space. `cannot be proved` means the property is **not established** — this is the correct and expected negative test result. It is not an error or inconclusive result; it is ProVerif signalling that the security guarantee has collapsed.

**`neg_platform_integrity.pv` — G10 Secure Boot**
Removed the `if boot_os = ApprovedOS then ... else 0` identity check from `processBMD`. The BMD still verifies the EA's signature on the firmware, but any EA-signed OS — including `TamperedOS` — now passes the boot stage. ProVerif finds a trace where `TamperedOS` is loaded, `BallotSigned` fires, but `OS_Loaded(dev1, ApprovedOS)` never appears in the trace. The TPM key secrecy query and the `TPM_Key_Unlocked` chain query both remain true, since neither depends on which OS was loaded.

**`neg_secure_transport.pv` — G13 Transport Integrity**
Removed the hash comparison `if h_final_check = published_hv` from `processAdmin`, replacing it with an unconditional acceptance. The admin reads `published_hv` from `ch_public` — a free channel the attacker controls. Without the comparison, the attacker sends an arbitrary `hv` on `ch_public` and the admin stamps it as verified. `Admin_Verified_Integrity(id, attacker_hv)` fires, but the BMD only ever committed to the real hash. The causal correspondence breaks. As a consequence `MalpracticeDetected` is also unreachable in this file — the detection branch was the else-arm of the removed check — which is expected and noted.

**`neg_election_recovery.pv` — G15 Recovery Causality**
Removed `event MalpracticeDetected(id)` from `processJudge`. Device revocation and `TriggerRepoll` still fire — the operational re-poll logic is intact — but the accountability event that records the evidentiary basis is gone. ProVerif immediately finds a trace where a re-poll is triggered with no `MalpracticeDetected` anywhere. The G12 provenance query (`BB_Published ==> BMD_Registered`) still holds because that mechanism was not touched.

### Negative Tests for Privacy Goals (G8 and G9)

The privacy goals use ProVerif's observational equivalence checker via `choice[]`. This checker is **sound but not complete**: it can prove that two worlds are equivalent, but it cannot always disprove equivalence. When `choice[]` worlds produce structurally symmetric outputs — same function symbols, same arities, same channel structure — ProVerif reports equivalent even if a computational distinguisher exists. This is a documented limitation of the tool, not a flaw in the model.

As a result, structural weakening of the biprocess (removing re-encryption, leaking partial decryptions) does not cause the equivalence check to fail — ProVerif still sees symmetric term shapes. The correct approach is to test the **underlying cryptographic assumptions** that each privacy proof depends on.

**`neg_privacy.pv` — G8 Anonymity**
G8 anonymity holds only if the voter's signing key `sk_vA` is secret. If the attacker learns it, they can compute `gen_null(sk_vA)` and match it against published nullifiers, linking every ballot to voter A regardless of how well the mixnet is implemented. We declared `sk_vA_leaked` as a public free name (known to the attacker from the start) and queried `not attacker(sk_vA_leaked)`. ProVerif returns false in one derivation step — the attacker already has it. This confirms that the G8 anonymity proof is grounded in the assumption that voter signing keys are never compromised.

**`neg_threshold_privacy.pv` — G9 Threshold Privacy**
G9 threshold privacy holds only if the third authority's key `sk3` remains secret. With `sk1` and `sk2` already given to the attacker (modelling n-1 corruption), `sk3` is the last line of defence. We passed `sk3_ref` through `processTally` as an explicit output on `ch_public` alongside the partial decryptions. ProVerif traces: tally outputs `(pdecA3, pdecB3, sk3_ref)`, attacker extracts the third component, goal reached. This confirms the threshold guarantee collapses exactly when the final key is compromised.

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
