# Threat Model — OpenVoting+
**Protocol:** OpenVoting+ (extends OpenVoting with preferential IRV voting, biometric token
issuance, and hardware-bound BMD attestation)
**Verification tool:** ProVerif 2.05, Dolev-Yao symbolic model
**Date:** 2026-03-26

---

## 1. System Overview & Trust Boundaries

```
┌───────────────────────────────────────────────────────────────────┐
│ ELECTION AUTHORITY (EA)                                           │
│  Key generation, ballot configuration, BMD provisioning          │
└───────────────────────────┬───────────────────────────────────────┘
                            │ signed firmware + ballot config (TLS)
                ┌───────────▼──────────────┐
                │   BMD j  (polling booth) │  ← hardware-bound TPM key
                │   Secure Boot + dm-verity│
                └──────┬───────────┬───────┘
             RFID token │           │ encrypted ballot + hash chain
                        │           │
 ┌──────────────────────▼─┐   ┌────▼──────────────────────┐
 │ Token Generation        │   │ Backend / Mix Servers      │
 │ Terminal (AS)           │   │ Bulletin Boards R,C,V,P    │
 │ Biometric + MongoDB CAS │   │ Tally Authorities (n-of-n) │
 └─────────────────────────┘   └───────────────────────────┘
```

### Trust Assumptions
| Component | Trusted for | Not trusted for |
|-----------|------------|-----------------|
| EA | Key generation, ballot config | Post-election manipulation |
| BMD (with ApprovedOS) | Honest vote recording, receipt signing | None — modeled as trusted after secure boot |
| BMD (with TamperedOS) | Nothing | G10 proves this is rejected |
| Token Generation Terminal | Face biometric + liveness check | Colluding with specific voter |
| Central MongoDB server | CAS atomicity for token issuance | Privacy of voter-token link |
| Mix servers | At least 1 of m is honest | All mix servers colluding |
| Tally authorities | At least 1 of n is honest | n-1 authorities colluding |
| Bulletin boards | Append-only, publicly readable | Write authentication (currently free channel in models) |
| Judge | Protocol-compliant | Being bribed |
| Network | Nothing — full Dolev-Yao attacker |  |

---

## 2. Threat Actor Catalogue

| ID | Actor | Capabilities |
|----|-------|-------------|
| DY | Dolev-Yao network attacker | Intercept, replay, modify, inject on all public channels |
| CA | Corrupt authentication terminal operator | Bypass biometric, issue tokens fraudulently |
| CB | Corrupt / tampered BMD | Modified OS, wrong receipt, ballot substitution |
| CAdmin | Corrupt election admin | Tamper USB payload before hash-chain verification |
| CMix | Corrupt mix server(s) | Drop ballots, wrong shuffle proof |
| CTally | Corrupt tally authority(ies) | Wrong partial decryption |
| VDouble | Voter attempting double voting | Token replay, credential reuse |
| VCoerce | Voter under coercion | Show receipt to coercer |
| TForge | Token forger (knows public params) | Forge RFID token without AS involvement |

---

## 3. Threat Analysis by Protocol Phase

### Phase A: Voter Authentication

| ID | Threat | Actor | Mechanism | Covered by model? | Notes |
|----|--------|-------|-----------|-------------------|-------|
| T-A1 | Double token issuance (concurrent) | CA / VDouble | Attacker starts two concurrent authentications | ✅ `voter_eligibility.pv` G6 — CAS atomicity | |
| T-A2 | Biometric spoofing (photo/video) | CA | Bypass SilentFace liveness | ❌ NOT modeled | Cannot be expressed in ProVerif; procedural defense only |
| T-A3 | RA key compromise → forge credentials | CA | Learn `sk_ra` | ✅ `voter_eligibility.pv` G11 — key secrecy | |
| T-A4 | RFID token relayed to wrong booth | DY | Intercept token, replay at different BMD | ⚠️ **GAP** — `token_booth_binding.pv` needed | RSA-OAEP provides binding but not formally proven |
| T-A5 | RFID token forged from public params | TForge | Construct `enc((vid, eid, booth_j), pk_bmd_j, s)` from public data | ⚠️ **CRITICAL GAP** — see §4.1 | vid and eid are public; attacker knows booth assignment formula |
| T-A6 | Token payload tampered in transit | DY | Modify RFID bytes in transit | ✅ Implicit — RSA-OAEP ciphertext integrity | Not explicitly modeled but follows from IND-CCA2 |
| T-A7 | mTLS channel between AS and server compromised | DY | MITM on token confirmation | ❌ NOT modeled | Assumed secure channel; outside ProVerif scope |
| T-A8 | Stale lock (crashed terminal) exploited | VDouble | Second terminal claims lock after timeout | ✅ `voter_eligibility.pv` — timeout auto-revert | |

### Phase C: Vote Casting

| ID | Threat | Actor | Mechanism | Covered? | Notes |
|----|--------|-------|-----------|----------|-------|
| T-C1 | BMD signs receipt for vote X but submits vote Y to BB | CB | Dishonest BMD | ✅ G1 `process_judge.pv` — detected via receipt dispute | Detection, not prevention |
| T-C2 | Voter shows receipt to coercer | VCoerce | TPM-signed receipt proves vote | ❌ KNOWN NON-GOAL | Receipt-freeness deliberately sacrificed for verifiability tradeoff |
| T-C3 | Token replayed at same booth for second vote | VDouble | Re-insert RFID card | ✅ G6 — nullifier blocks second ballot acceptance | **In formal model only** — actual implementation relies on server-side check |
| T-C4 | BMD encodes different preference ordering than selected | CB | IRV preference vector substitution | ⚠️ **GAP** — no IRV model | G1 covers single-choice; preference vector encoding not verified |
| T-C5 | BMD logs voter_id alongside vote, violating anonymity | CB | Internal logging by compromised BMD | ⚠️ **DISCREPANCY** — see §4.2 | G8 model uses ZKP (stronger than actual RSA-OAEP token) |
| T-C6 | Voter forced to vote in a specific way under observation | VCoerce | Physical coercion at booth | ❌ OUT OF SCOPE | Physical security measure |

### Phase H: Hash Chain / USB Transport

| ID | Threat | Actor | Mechanism | Covered? | Notes |
|----|--------|-------|-----------|----------|-------|
| T-H1 | Admin inserts/deletes/reorders votes in USB | CAdmin | Modify USB payload | ✅ G13 `secure_transport.pv` | |
| T-H2 | Admin replaces entire USB with another device's data | CAdmin | Different device_id payload | ✅ G13 — TPM seal includes device_id | |
| T-H3 | BMD publishes wrong hash commitment (pre-tampering) | CB | Malicious hash publication | ⚠️ Minor gap | Mitigated by G10 (secure boot prevents tampered BMD) |
| T-H4 | Hash collision enables undetected substitution | DY | Cryptanalysis of SHA-256 | ✅ Cryptographic assumption | |

### Phase T: Mix / Tally

| ID | Threat | Actor | Mechanism | Covered? | Notes |
|----|--------|-------|-----------|----------|-------|
| T-T1 | Mix server drops ballots | CMix | Omit ciphertext from output | ✅ G15 `election_recovery_master.pv` — detected, triggers recovery | |
| T-T2 | Mix server reveals permutation | CMix | Publish permutation | ✅ G8 `privacy.pv` — re-encryption prevents linkability | |
| T-T3 | Mix server publishes false shuffle proof | CMix | Cheating on ZK proof | ⚠️ **GAP** — shuffle proof verification not modeled | NIZK soundness assumed |
| T-T4 | All mix servers collude | CMix | Full collusion | ❌ NOT modeled | Requires at least 1 honest mix server (threshold assumption) |
| T-T5 | n-1 tally authorities collude on partial decryptions | CTally | Reconstruct key from n-1 shares | ✅ G9 `threshold_privacy.pv` | |
| T-T6 | IRV elimination round manipulated in tally | CTally | Declare wrong candidate as weakest | ⚠️ **GAP** — IRV not modeled | G4 (tally correctness) is out of scope for ProVerif |

### Phase R: Audit / Recovery

| ID | Threat | Actor | Mechanism | Covered? | Notes |
|----|--------|-------|-----------|----------|-------|
| T-R1 | Judge triggers re-poll without malpractice evidence | Judge | Unauthorized re-poll | ✅ G15 `election_recovery_master.pv` | |
| T-R2 | Voter falsely claims ballot missing from BB | VDouble | Fraudulent dispute | ✅ G3 — judge verifies TPM receipt | |
| T-R3 | Revocation list tampered post-revocation | DY | Modify RevocationList table | ❌ Minor gap | Table is internal in model; authenticated BB mitigates in practice |

---

## 4. Critical Gaps — Detailed Analysis

### 4.1 Token Forgeability (T-A5) — CRITICAL

**The problem:**
Voter IDs are public (electoral roll). Eligibility vectors can be inferred or are semi-public.
Booth assignment is deterministic: `j = (H(vid ‖ encode(eid)) mod l) + 1`.
BMD public keys are distributed openly.
Therefore, an attacker can compute `j` and construct:
```
forged_token = enc((vid, eid, j, random_tid, ts), pk_bmd_j, fresh_seed)
```
This is a syntactically valid RSA-OAEP ciphertext. The BMD decrypts it, checks `booth = j` ✓, and loads the ballot — **without verifying the token was actually issued by the AS**.

**The crucial question:** Does the BMD contact the AS/central server after decryption to verify `token_id`?
- If YES → forged tokens are rejected (server has no record of `random_tid`)
- If NO → token injection is possible, enabling ballot stuffing

**Mitigation in the formal model:** `voter_eligibility.pv` uses ZKP credentials that cannot be forged without `sk_ra` (G11). The forged token attack does not apply to the formal model because the formal model does not use the RSA-OAEP token — it uses an unforgeable ZKP credential.

**ACTION:** New model `token_booth_binding.pv` verifies booth-binding; the AS_Issued provenance query detects forgeability if the AS leaks any token derivation capability.

### 4.2 Anonymity Discrepancy (T-C5) — SIGNIFICANT

**The problem:**
G8 (`privacy.pv`) proves observational equivalence using ZKP credentials where the voter's identity is never revealed — even the credential is anonymous (`prove_membership(sk_v, cred)` contains no `pk_v`).

The **actual implementation** uses:
```
token = RSA-OAEP-enc(pk_bmd_j, (vid, eid, j, tid, ts))
```
The BMD decrypts this and learns `vid`. Anonymity depends on the BMD:
1. Not logging `vid` alongside the vote
2. Erasing `vid` from volatile memory after ballot loading
3. The AS erasing the `vid → token_id` mapping after issuance

This is **procedural unlinkability**, not **cryptographic unlinkability**. The G8 proof establishes stronger anonymity than the real system provides.

**Consequence:** If the BMD is compromised (e.g., TamperedOS slips through), it could log `(vid, encrypted_vote)` pairs, linking voters to ballots. G10 (secure boot) is the defense — a tampered BMD cannot sign ballots.

**Conclusion:** G8 ∧ G10 together provide the anonymity guarantee. Neither alone is sufficient.

### 4.3 Receipt-Freeness — KNOWN NON-GOAL

The protocol issues a TPM-signed receipt `sign_receipt(ballot, session_id, sk_tpm)` to the voter. This receipt:
- ✅ Enables dispute (G3)
- ✅ Proves ballot was cast-as-intended (G1)
- ❌ Can be shown to a coercer to prove how one voted

Receipt-freeness requires the voter to be unable to prove their vote to a third party. This is **intentionally sacrificed** in this protocol design in exchange for individual verifiability. This tradeoff must be explicitly stated in the paper.

---

## 5. ProVerif Model Coverage Summary

| Goal | File | Status |
|------|------|--------|
| G1 Cast-as-intended | process_judge.pv | ✅ Proven |
| G2 Recorded-as-cast | process_judge.pv | ✅ Proven |
| G3 Dispute soundness | process_judge.pv | ✅ Proven |
| G4 Tally correctness | — | ❌ Out of scope (ProVerif cannot model Paillier/IRV arithmetic) |
| G5 Eligibility | voter_eligibility.pv | ✅ Proven (ZKP model) |
| G6 One-person-one-vote | voter_eligibility.pv | ✅ Proven (nullifier — formal model only) |
| G7 Ballot secrecy | privacy_secrecy.pv | ✅ Proven |
| G8 Anonymity | privacy.pv | ✅ Proven (ZKP model — stronger than implementation) |
| G9 Threshold privacy | threshold_privacy.pv | ✅ Proven |
| G10 Platform integrity | platform_integrity.pv | ✅ Proven |
| G11 Key secrecy | voter_eligibility.pv + platform_integrity.pv | ✅ Proven |
| G12 Ballot provenance | election_recovery_master.pv | ✅ Proven |
| G13 Transport integrity | secure_transport.pv | ✅ Proven |
| G14 Device revocation | election_recovery_master.pv | ✅ Proven |
| G15 Localized recovery | election_recovery_master.pv | ✅ Proven |
| G-TB Token booth-binding | token_booth_binding.pv | ⚠️ NEW — see models/ |
| G-RF Receipt-freeness | — | ❌ Explicit non-goal |

---

## 6. New Models Added (This Session)

1. **`models/token_booth_binding.pv`** — Verifies RSA-OAEP token mechanism:
   - G-TB1: Token decrypted at booth j must have been issued for booth j (AS provenance)
   - G-TB2: BMD private keys non-extractable
   - G-TB3: Cross-booth relay impossible (wrong-key decryption fails)
   - Negative test: `negative_tests/neg_token_booth_binding.pv` — removing booth-id check breaks provenance

2. **`THREAT_MODEL.md`** (this file) — Full threat matrix

---

## 7. Residual Risks (Accepted)

| Risk | Acceptance Reason |
|------|------------------|
| Biometric spoofing (T-A2) | Hardware defense (SilentFace + Dlib); outside ProVerif scope |
| All mix servers collude (T-T4) | Standard threshold assumption; equivalent to OpenVoting |
| Receipt-freeness (T-C2) | Intentional design tradeoff for verifiability |
| IRV tally manipulation (T-T6) | G4 out of scope for symbolic verification; arithmetic proof needed |
| Physical coercion at booth (T-C6) | Physical security measure |
| Judge corruption | Institutional trust assumption |
