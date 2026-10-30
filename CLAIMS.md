# Klaim

Hanya klaim proposal yang benar-benar punya pasangan di repo ini. Semua status
di bawah sudah dicek dengan `dune build`; tidak ada `Admitted` atau `Axiom`.

| Klaim di proposal | Aturan (`rules.md`) atau lemma | File | Status |
|-------------------|--------------------------------|------|--------|
| §11 Bacaan logis: `submit : A ⊸ ◇ₖA` | aturan `submit` | `docs/rules.md`, `theories/Sequent.v` | ada sebagai aturan |
| §11 await sebagai satu-satunya jalan memakai isi future, dalam bentuk lax bergraded | aturan `await` | `docs/rules.md`, `theories/Sequent.v` | ada sebagai aturan |
| §11 cancel adalah aksi protocol, bukan destruksi: resource tetap di dalam future | aturan `cancel` | `docs/rules.md`, `theories/Sequent.v` | ada sebagai aturan |
| §11 ◇ₖA tidak bisa menjadi A tanpa await | `dia_not_elim` | `theories/Examples.v` | terbukti untuk setiap A tanpa ◇; batasan itu perlu (`dia0_dia`) |
| §11 cancel tidak menambah kekuatan logis (pertanyaan riset) | `cancel_admissible` | `theories/Examples.v` | terbukti: cancel diturunkan dari submit, await, dan cut |
| §11 Syarat Curry-Howard 1: sequent calculus dengan aturan yang bisa dibenarkan tanpa menyebut program | `docs/rules.md` | `docs/rules.md`, `theories/Sequent.v` | ada, untuk fragmen 1, ⊗, ⊸, ⊕, ◇ₖ |
| §11 Basis dan langkah, langkah 1: "tambahkan aturan cancel pada future linear dan buktikan cut elimination" | `cut_admissible` | `theories/CutElim.v` | terbukti (cut admissibility, bukan cut elimination sebagai eksekusi), tanpa semantik biaya dan tanpa mode adjoint |
| §11 Konjektur (1): cut elimination berlaku | `cut_admissible` | `theories/CutElim.v` | hanya bagian "berlaku", untuk fragmen ini; "berkorespondensi dengan eksekusi I/O asinkron" belum diformalkan |
| §11 Bacaan logis: `free : A ⊸ 1`, free hanya menerima A | hipotesis `free` di `sanity_submit_cancel_await_free` | `theories/Examples.v` | sanity check saja, bukan hasil; goal-nya ◇ₖ1 karena await lax |
