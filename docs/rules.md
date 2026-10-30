# Aturan inferensi

File ini adalah sumber kebenaran untuk `theories/Sequent.v`. Setiap aturan di
bawah punya tepat satu konstruktor dengan nama yang sama di `Sequent.v`, dan
sebaliknya.

## Formula

```
A, B ::= p | 1 | A ⊗ B | A ⊸ B | A ⊕ B | ◇ₖA        (p atom, k : nat)
```

## Sequent

```
Δ ⊢ C
```

`Δ` adalah konteks linear, ditulis sebagai list formula. Urutan di list tidak
bermakna secara logis; exchange diberikan sebagai satu aturan eksplisit
(`exchange`). Aturan kiri selalu bekerja pada formula di kepala list. Konteks
yang dipecah ditulis `Δ₁, Δ₂` (konkatenasi list).

Tidak ada weakening dan tidak ada contraction. Tidak ada aturan cut; cut
adalah teorema (`cut_admissible` di `CutElim.v`).

## Aturan

### Identitas dan struktural

```
  ─────────── id_atom
    p ⊢ p


    Δ ⊢ C      Δ adalah permutasi dari Δ'
  ───────────────────────────────────────── exchange
    Δ' ⊢ C
```

`id_atom` hanya untuk atom. `A ⊢ A` untuk formula sembarang adalah teorema
(`identity` di `Identity.v`).

### Unit 1

```
  ─────── one_R
    ⊢ 1


    Δ ⊢ C
  ─────────── one_L
   1, Δ ⊢ C
```

### Tensor ⊗

```
   Δ₁ ⊢ A     Δ₂ ⊢ B
  ──────────────────── tensor_R
    Δ₁, Δ₂ ⊢ A ⊗ B


   A, B, Δ ⊢ C
  ────────────── tensor_L
   A ⊗ B, Δ ⊢ C
```

### Implikasi linear ⊸

```
   A, Δ ⊢ B
  ──────────── lolli_R
   Δ ⊢ A ⊸ B


   Δ₁ ⊢ A     B, Δ₂ ⊢ C
  ─────────────────────── lolli_L
   A ⊸ B, Δ₁, Δ₂ ⊢ C
```

### Plus ⊕

```
     Δ ⊢ A
  ─────────── plus_R1
   Δ ⊢ A ⊕ B


     Δ ⊢ B
  ─────────── plus_R2
   Δ ⊢ A ⊕ B


   A, Δ ⊢ C     B, Δ ⊢ C
  ─────────────────────── plus_L
       A ⊕ B, Δ ⊢ C
```

### Future ◇ₖ

```
    Δ ⊢ A
  ────────── submit          (◇ₖ-kanan, untuk setiap k)
   Δ ⊢ ◇ₖA


      A, Δ ⊢ ◇ⱼC
  ────────────────── await   (◇ₖ-kiri, lax bergraded)
   ◇ₖA, Δ ⊢ ◇₍ₖ₊ⱼ₎C


   ◇ₖ(R ⊗ (X ⊕ 1)), Δ ⊢ C
  ───────────────────────── cancel
     ◇ₖ(R ⊗ X), Δ ⊢ C
```

Catatan:

- `submit` membaca `submit : A ⊸ ◇ₖA`. Grade k bebas dipilih.
- `await` adalah aturan lax: isi future (A) hanya boleh dipakai bila goal juga
  sebuah future. Grade-nya dijumlahkan: menunggu future bergrade k lalu
  menjalankan sisa yang bergrade j memberi future bergrade k + j. Akibatnya
  ◇ₖA tidak lagi setara dengan A.
- `cancel` bekerja pada future yang membawa resource R dan hasil X. Setelah
  cancel, hasilnya menjadi X ⊕ 1 (selesai, atau dibatalkan tanpa hasil),
  sedangkan R tetap ada di dalam future: cancel tidak pernah mengembalikan R
  atau X keluar dari ◇ₖ.
- `free : A ⊸ 1` bukan aturan logika. Di `Examples.v` ia muncul sebagai
  hipotesis `buf ⊸ 1` di konteks.

## Teorema tentang aturan (bukan aturan)

| Nama | Pernyataan | File |
|------|------------|------|
| `identity` | `A ⊢ A` untuk setiap A | `Identity.v` |
| `dia_mono` | bila `Δ ⊢ ◇ⱼC` dan `j ≤ n`, maka `Δ ⊢ ◇ₙC` | `CutElim.v` |
| `cut_admissible` | bila `Δ₁ ⊢ A`, `Γ ⊢ C`, Γ permutasi dari `A', Δ₂`, dan A' adalah A dengan sebagian subformula positif X diganti X ⊕ 1 (`ext A A'`), maka `Δ₁, Δ₂ ⊢ C` | `CutElim.v` |
| `cut` | bila `Δ₁ ⊢ A` dan `A, Δ₂ ⊢ C`, maka `Δ₁, Δ₂ ⊢ C` | `CutElim.v` |
| `cancel_admissible` | aturan `cancel` bisa diturunkan dari `submit`, `await`, dan `cut` | `Examples.v` |
