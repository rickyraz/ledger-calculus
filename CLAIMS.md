# Klaim

Hanya klaim proposal (`docs/ledger-calculus.pdf`) yang benar-benar punya
pasangan di repo ini. Semua status di bawah sudah dicek dengan `dune build`;
tidak ada `Admitted` atau `Axiom`.

| Klaim di proposal | Aturan (`rules.md`) atau lemma | File | Status |
|-------------------|--------------------------------|------|--------|
| §11 Bacaan logis: `submit : A ⊸ ◇ₖA` | aturan `submit` | `docs/rules.md`, `theories/Sequent.v` | ada sebagai aturan |
| §11 Bacaan logis: `await : ◇ₖA ⊸ A` | aturan `await`; `dia_elim_via_await` | `theories/Sequent.v`, `theories/Examples.v` | ada sebagai aturan; `◇ₖA ⊢ A` terbukti derivable lewat await |
| §11 Bacaan logis: `cancel : ◇ₖA ⊸ ◇ₖA`, "cancel adalah aksi protocol, bukan destruksi" | aturan `cancel` | `docs/rules.md`, `theories/Sequent.v` | ada sebagai aturan; tidak menambah teorema (premis = kesimpulan) |
| §11 "Logika ini tidak punya aturan ◇A ⊢ A selain lewat await" | `dia_atom_not_elim_without_await` | `theories/Examples.v` | terbukti untuk A atomik di fragmen tanpa await; A sembarang terbuka |
| §11 Syarat Curry-Howard 1: sequent calculus dengan aturan yang bisa dibenarkan tanpa menyebut program | `docs/rules.md` | `docs/rules.md`, `theories/Sequent.v` | ada, untuk fragmen 1, ⊗, ⊸, ◇ₖ |
| §11 Basis dan langkah, langkah 1: "tambahkan aturan cancel pada future linear dan buktikan cut elimination" | `cut_admissible` | `theories/CutElim.v` | terbukti (cut admissibility, bukan cut elimination sebagai eksekusi), tanpa grade dan tanpa mode adjoint |
| §11 Konjektur (1): cut elimination berlaku | `cut_admissible` | `theories/CutElim.v` | hanya bagian "berlaku", untuk fragmen ini; "berkorespondensi dengan eksekusi I/O asinkron" belum diformalkan |
| §11 Bacaan logis: `free : A ⊸ 1`, free hanya menerima A | hipotesis `free` di `sanity_submit_cancel_await_free` | `theories/Examples.v` | sanity check saja, bukan hasil |
