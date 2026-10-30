# ledger-calculus

Artefak riset untuk teori Ledger Calculus: sequent calculus kecil untuk
*cancellable linear futures*, dengan bukti di Rocq. Repo ini berisi teori dan
bukti, bukan tooling.

Sumber kebenaran untuk istilah, notasi, klaim, dan referensi adalah proposal
[`docs/ledger-calculus.pdf`](docs/ledger-calculus.pdf). Aturan inferensi yang
diformalkan ada di [`docs/rules.md`](docs/rules.md).

## 1. Apa ini

Dari Ringkasan proposal: Ledger Calculus adalah program riset, bukan teori
yang sudah mapan. Gagasannya, setiap program diperlakukan sebagai entri buku
besar: nilai, ownership, protocol, effect, dan biaya dicatat dalam satu
derivasi, dan setiap komposisi harus "balance". Repo ini hanya menggarap satu
potongan kecil dari program itu, yaitu arah fundamental di bagian 11:
logika untuk future linear yang bisa di-cancel tanpa melepaskan resource-nya.

## 2. Konjektur inti

Dikutip dari bagian 11 proposal (simbol ◇ₖ dipulihkan dari PDF):

> Ada adjoint logic bergraded dengan modality pinjaman ◇ₖ dan aturan cancel di
> atas, sehingga (1) cut elimination berlaku dan berkorespondensi dengan
> eksekusi I/O asinkron, (2) panjang normalisasi dibatasi grade, dan (3) bebas
> deadlock, bebas use-after-free, serta batas memori yang ditahan adalah
> korolari cut elimination.

Repo ini **tidak** membuktikan konjektur itu. Ia hanya membuktikan cut
admissibility untuk fragmen yang jauh lebih kecil (lihat bagian 3 dan 5).

## 3. Yang diformalkan di repo ini

Fragmen intuitionistic linear logic dengan 1, ⊗, ⊸, ⊕, ditambah modality ◇ₖ
(k : nat) dengan tiga aturan:

| Aturan di `rules.md` | Bentuk |
|----------------------|--------|
| `submit` (◇ₖ-kanan) | Δ ⊢ A ⟹ Δ ⊢ ◇ₖA |
| `await` (◇ₖ-kiri, lax bergraded) | A, Δ ⊢ ◇ⱼC ⟹ ◇ₖA, Δ ⊢ ◇₍ₖ₊ⱼ₎C |
| `cancel` | ◇ₖ(R ⊗ (X ⊕ 1)), Δ ⊢ C ⟹ ◇ₖ(R ⊗ X), Δ ⊢ C |

Di versi `v0-baseline`, `await` adalah aturan kiri biasa, sehingga ◇ₖA setara
dengan A dan modality-nya tidak punya isi. Sekarang `await` lax: isi future
hanya bisa dipakai bila goal juga future, sehingga ◇ₖA ⊬ A untuk A tanpa ◇
(`dia_not_elim`).

Sistem ini adalah **penyederhanaan** dari adjoint logic Pruiksma & Pfenning
([Back to Futures](https://arxiv.org/abs/2002.04607)), bukan instansnya:

- Hanya ada satu mode (linear). Tidak ada hierarki mode, tidak ada shift ↑/↓,
  dan tidak ada mode yang mengizinkan weakening atau contraction.
- ◇ₖ adalah modality lax primitif dengan aturan sendiri, bukan hasil komposisi
  shift seperti future di adjoint logic.
- Tidak ada term assignment, tidak ada semantik operasional, dan tidak ada
  concurrency. Cut admissibility di sini adalah teorema tentang derivabilitas,
  bukan korespondensi dengan eksekusi.
- Grade k punya isi proof-theoretic: `await` menjumlahkannya, dan `dia_mono`
  menunjukkan bahwa ia berperilaku sebagai batas atas. Grade belum punya
  semantik biaya; itu masuk bersama aturan biaya di tahap berikutnya.

Konteks linear adalah `list form`, dengan aturan `exchange` eksplisit
(berdasarkan `Permutation` dari stdlib Rocq). Relasi derivasi adalah
`seq Δ C`, tanpa parameter.

Rocq murni: hanya stdlib, tanpa Iris, tanpa library pihak ketiga, tanpa
`Axiom`.

## 4. Status

Semua lemma terbukti. Tidak ada `Admitted` dan tidak ada `Axiom`;
`Print Assumptions` untuk setiap teorema di bawah mencetak
`Closed under the global context`.

| Lemma | File | Status | Bergantung pada |
|-------|------|--------|-----------------|
| `identity` : ∀A, `[A] ⊢ A` | `Identity.v` | terbukti | kasus ◇ₖ: `await k` di atas `submit 0` |
| `perm_cons_split`, `perm_app_split`, `perm_front`, `perm_to_front` | `CutElim.v` | terbukti | stdlib `Permutation` |
| `ext`, `ext_refl`, lemma inversi `ext_*_inv`, `ext_cancel_step` | `CutElim.v` | terbukti | - |
| `dia_mono` : `Δ ⊢ ◇ⱼC`, `j ≤ n` ⟹ `Δ ⊢ ◇ₙC` | `CutElim.v` | terbukti | - |
| `cut_E` (induksi pada derivasi kanan) | `CutElim.v` | terbukti | lemma permutasi, `ext`, `dia_mono` |
| `cut_aux` (induksi pada ukuran formula dan derivasi kiri) | `CutElim.v` | terbukti | `cut_E` |
| `cut_admissible` : ∀A, `cut_stmt A` | `CutElim.v` | terbukti | `cut_aux` |
| `cut` (formula cut di kepala) | `CutElim.v` | terbukti | `cut_admissible`, `ext_refl` |
| `dia_free_inv` (invariant inversi) | `Examples.v` | terbukti | - |
| `dia_not_elim` : A tanpa ◇ ⟹ `¬ ([◇ₖA] ⊢ A)` | `Examples.v` | terbukti | `dia_free_inv` |
| `dia0_dia` : `[◇₀(◇ⱼB)] ⊢ ◇ⱼB` | `Examples.v` | terbukti | `identity` |
| `cancel_admissible` | `Examples.v` | terbukti | `cut`, `identity` |
| `sanity_submit_cancel_await_free` (sanity check, bukan hasil) | `Examples.v` | terbukti | `cut` |

**◇ₖA ⊬ A.** `dia_not_elim` dibuktikan pada sistem cut-free lewat invariant
`dia_free_inv`: bila goal tanpa ◇ dan setiap formula konteks tanpa ◇ atau
berbentuk ◇ di puncak, maka konteksnya sama sekali tanpa ◇. Hanya `submit` dan
`await` yang menghasilkan goal ◇, dan `cancel` mempertahankan ◇ di puncak.
Karena `cut_admissible` terbukti, hasil ini juga berlaku untuk sistem dengan
cut. Batasan "A tanpa ◇" perlu: `dia0_dia` menunjukkan ◇₀(◇ⱼB) ⊢ ◇ⱼB.

**Apakah `cancel` admissible dari `submit` + `await`?** Ya, dengan cut.
◇ₖ(R ⊗ X) ⊢ ◇ₖ(R ⊗ (X ⊕ 1)) diturunkan dengan `await k` di atas `submit 0`
(grade k + 0 = k), lalu di-cut dengan premis `cancel`
(`cancel_admissible`, tanpa memakai konstruktor `cancel`). Jadi cancel tidak
menambah kekuatan logis: setiap sequent yang diturunkan dengan cancel juga
diturunkan dari submit, await, dan cut. Catatan jujur: `cut_admissible`
dibuktikan untuk sistem yang memuat `cancel`. Pernyataan "sistem tanpa
konstruktor `cancel` menurunkan sequent yang sama" butuh cut admissibility
untuk sistem tanpa cancel; buktinya sama (kasus `cancel` di `cut_E` dan
`cut_aux` hanya mengomutasikan cancel yang sudah ada), tetapi belum
diformalkan sebagai sistem terpisah.

## 5. Terbuka

Tidak ada `Admitted`. Strategi bukti cut admissibility:

- Induksi luar pada ukuran formula cut di sisi kiri (`size A`, `cut_aux`).
- Di dalamnya, induksi struktural pada derivasi kiri `Δ₁ ⊢ A`. Aturan kiri
  selain `await`, `cancel`, dan `exchange` di sisi kiri dikomutasikan langsung.
- Bila derivasi kiri berakhir dengan aturan kanan, `id_atom`, atau `await`,
  premisnya dicatat di `rinfo`, lalu dilakukan induksi struktural pada
  derivasi kanan (`cut_E`). Induksi struktural pada derivasi menggantikan
  induksi pada tinggi derivasi.
- `await` di sisi kiri tidak bisa langsung dikomutasikan, karena aturannya
  butuh goal berbentuk future. Ia ditangani saat derivasi kanan principal
  pada formula cut dengan `await`: cut dipindah ke premis `await` kiri, lalu
  `await` diterapkan lagi dengan grade (k₁ + j₁) + j = k₁ + (j₁ + j).
- Kasus `submit` terhadap `await` menghasilkan ◇ⱼC padahal yang dibutuhkan
  ◇₍ₖ₊ⱼ₎C; `dia_mono` menaikkan grade.
- Titik yang hampir macet: `cancel` di sisi kanan mengganti formula cut
  ◇ₖ(R ⊗ X) dengan ◇ₖ(R ⊗ (X ⊕ 1)), yang lebih besar, sehingga induksi pada
  ukuran formula gagal. Solusinya, formula cut di sisi kanan boleh berupa A'
  dengan `ext A A'` (A dengan sebagian subformula positif X diganti X ⊕ 1),
  dan ukuran induksi tetap ukuran A di sisi kiri. `ext` sengaja tidak masuk
  ke antecedent ⊸, supaya ukuran tidak bertambah di posisi negatif.
- Cut dirumuskan untuk konteks kanan yang merupakan permutasi dari `A', Δ₂`,
  sehingga kasus `exchange` tidak macet.

Yang belum dikerjakan:

- Sistem tanpa `cancel` sebagai inductive terpisah, untuk menyatakan
  "cancel tidak menambah kekuatan logis" tanpa melewati cut di sistem
  yang memuat cancel (lihat bagian 4).
- Cut elimination sebagai eksekusi (term assignment), semantik biaya untuk
  grade, batas panjang normalisasi, dan model kategori (bagian 11, langkah 2
  sampai 4).

## 6. Posisi

[Back to Futures](https://arxiv.org/abs/2002.04607) (Pruiksma & Pfenning,
JFP 2022) sudah memberi linear futures lewat Curry-Howard untuk adjoint logic;
proposal mencatat bahwa klaim "paper itu tidak memodelkan cancellation" masih
dugaan karena isinya belum dibaca lengkap. ◇ sebagai "eventually" sudah ada di
[Fair Reactive Programming](https://www.cs.mcgill.ca/~acave1/papers/fair-reactive-long.pdf)
(Cave dkk.) dan Lively RaTT
([Bahr dkk., POPL 2021](https://arxiv.org/abs/2003.03170)), tetapi untuk nilai
yang berubah terhadap waktu, bukan resource.
[Curry-Howard for destructors](https://arxiv.org/abs/2510.23517) (Congard,
Munch-Maccagnoni, Douence, 2025) memberi resource safety plus exception secara
Curry-Howard dan menyebut borrowing sebagai masalah terbuka. Repo ini **bukan**
logika baru yang setara dengan karya-karya itu, **bukan** bukti konjektur
bagian 11, dan **tidak** mengklaim kebaruan untuk fragmen ILL dengan 1, ⊗, ⊸, ⊕
maupun untuk cut admissibility-nya; kontribusinya hanya mekanisasi kecil dan
jujur dari aturan submit, await lax, dan cancel sebagai titik awal.

## 7. Hubungan dengan ZBeam

[ZBeam](https://github.com/rickyraz/zbeam) adalah Erlang Distribution peer
native di Zig dengan ownership eksplisit, berstatus MVP; io_uring dan arena
ownership masih ditandai "research only". Proposal memakainya sebagai pengguna
pertama dan bukti kelayakan: protocol buffer io_uring (Owned → InFlight →
Completed/Cancelled) adalah tempat aturan cancel di sini akan diuji. ZBeam
adalah studi kasus masa depan; modelnya akan masuk nanti di
`theories/case_studies/zbeam/`. Folder itu belum ada, dan repo ini tidak berisi
kode Zig.

## 8. Roadmap

Ringkasan bagian 10 proposal:

1. Fase 1: λ-Ledger sekuensial (ownership, effect, biaya W dan A) di Rocq di
   atas Iris dan time credits. Gate: adequacy terbukti.
2. Fase 2: protocol ala Actris, concurrency, biaya S, M, N, dan model ZBeam.
   Gate: demand-gated mailbox dan protocol at-most-once M2c terverifikasi.
3. Fase 3: kontrak Allocator dan std.Io untuk satu allocator (arena) dan dua
   backend Io. Gate: kedua backend setara perilakunya, hanya berbeda biaya.
4. Fase 4: checker Zig di atas ZIR/AIR, inference tingkat 0-1. Gate: modul
   mailbox/dispatcher ZBeam lolos tanpa bukti manual, dan leak di jalur
   errdefer pada test suite buatan tertangkap semua.
5. Fase 5: io_uring dan arena di ZBeam. Gate: cancellation-safe read
   terbukti, dan test SIGKILL/nodedown tetap lolos.

Repo ini berada sebelum fase-fase itu, di langkah 1 bagian 11 ("tambahkan
aturan cancel pada future linear dan buktikan cut elimination"), untuk fragmen
tanpa semantik biaya dan tanpa mode adjoint.

## 9. Build

Versi yang dipakai (dari mesin pengembangan, Rocq Platform 2026.07.0 di
Windows): Rocq 9.1.0 (`rocq --version`), dune 3.21.0 (`dune --version`),
rocq-stdlib 9.0.0 (package pick Rocq Platform 9.1~2026.01). dune juga butuh
compiler OCaml di PATH; di mesin pengembangan dipakai OCaml 4.14.2 dari opam
(versi yang sama dengan build Rocq Platform).

```bash
dune build
```

Di Windows dengan Rocq Platform, `dune` perlu `bin` Rocq Platform dan
`ocamlc` di PATH, serta `OCAMLPATH` yang menunjuk ke `lib` Rocq Platform,
misalnya (Git Bash):

```bash
PATH="$HOME/Rocq-platform-9.1/bin:$PATH:$LOCALAPPDATA/opam/ledger/bin" OCAMLPATH="$HOME/Rocq-platform-9.1/lib" dune build
```

Tanpa dune, file bisa dicek langsung dengan Rocq:

```bash
cd theories && for f in Syntax Sequent Identity CutElim Examples; do rocq compile -Q . LedgerCalculus $f.v; done
```

CI (`.github/workflows/ci.yml`) memakai image resmi `rocq/rocq-prover:9.1`
lewat `coq-community/docker-coq-action`. Image dengan tag 9.1.0 tidak ada, jadi
versi persis dipaksa lewat dependensi di `ledger-calculus.opam`.
