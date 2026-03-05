# VeriTraceMix: Formal Verification of an E2E Verifiable Voting Protocol

[![ProVerif](https://img.shields.io/badge/Verified%20with-ProVerif%202.04-blue)](https://bblanche.gitlabpages.inria.fr/proverif/)
[![Security](https://img.shields.io/badge/Properties-G1--G15-green)](#security-goals-mapping)
[![Build](https://img.shields.io/badge/Status-Verified-success)](#verification-results-summary)

## 📌 Project Overview
This repository contains the formal verification of **VeriTraceMix**, an end-to-end (E2E) verifiable electronic voting protocol. The protocol is designed to address the critical tension between **Voter Privacy** and **System Accountability**. 

Using **Applied Pi-Calculus** and the **ProVerif** automated reasoning tool, this project rigorously models the voting lifecycle and proves its resilience against a Dolev-Yao adversary. The model specifically focuses on hardware-assisted security using **Trusted Execution Environments (TEEs/TPMs)**.

## 🚀 Technical Highlights
- **Hardware Root of Trust:** Leverages TPM-bound non-extractable keys for ballot attestation.
- **Formal Methods:** Uses observational equivalence to prove voter anonymity and injective correspondence for integrity.
- **Localized Recovery (G15):** A unique formalization of a "Judge" process that allows for localized re-polls rather than total system failure upon malpractice detection.
- **Threshold Cryptography:** Models $n$-of-$m$ partial decryptions to ensure no single authority can compromise the tally.

---

## 📂 Repository Structure & Goal Mapping

The models are modularized to verify specific security goals (G1–G15) as defined in the Open-Voting framework:

| File | Security Goal | Description |
| :--- | :--- | :--- |
| `process_judge.pv` | **G1, G2, G3** | **Individual Verifiability:** Cast-as-intended & Recorded-as-cast. |
| `platform_integrity.pv` | **G4** | **Platform Integrity:** Secure Boot and TEE/TPM enforcement. |
| `voter_eligibility.pv` | **G5, G6** | **Eligibility:** One-person-one-vote using nullifiers & ZKPs. |
| `privacy.pv` | **G7, G8** | **Anonymity:** Observational equivalence via Re-encryption Mixnets. |
| `threshold_privacy.pv`| **G9** | **Resilience:** Security against $(n-1)$ corrupt tallying admins. |
| `secure_transport.pv` | **G13** | **Chain of Custody:** Hash-chaining for physical USB transport. |
| `election_recovery_master.pv` | **G14, G15** | **Accountability:** Malpractice detection & localized recovery. |

---

## 🛠 Usage & Verification

### Prerequisites
- [ProVerif 2.04+](https://proverif.inria.fr/) installed in your PATH.
- A Bash-compliant terminal (Linux, macOS, or WSL).

### Automated Verification Suite
Run the provided script to verify all properties and security goals at once:

```bash
chmod +x verify_all.sh
./verify_all.sh