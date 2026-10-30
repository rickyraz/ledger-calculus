# Aturan inferensi

File ini adalah sumber kebenaran untuk `theories/Sequent.v`. Setiap aturan di
bawah punya tepat satu konstruktor dengan nama yang sama di `Sequent.v`, dan
sebaliknya.

## Formula

```
A, B ::= p | 1 | A ⊗ B | A ⊸ B | ◇ₖA        (p atom, k : nat)
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

## Parameter fragmen `aw`

Relasi derivasi diberi satu parameter boolean `aw`. Hanya aturan `await` yang
memakainya: `await` hanya berlaku bila `aw = true`. Logika yang dimaksud
proposal adalah `aw = true`. Fragmen `aw = false` (logika tanpa `await`)
dipakai untuk menyatakan bahwa tidak ada aturan lain yang mengubah ◇ₖA
menjadi A.

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

### Future ◇ₖ

```
    Δ ⊢ A
  ────────── submit          (◇ₖ-kanan)
   Δ ⊢ ◇ₖA


   A, Δ ⊢ C
  ───────────── await        (◇ₖ-kiri; hanya bila aw = true)
   ◇ₖA, Δ ⊢ C


   ◇ₖA, Δ ⊢ C
  ───────────── cancel
   ◇ₖA, Δ ⊢ C
```

Catatan:

- `submit` membaca `submit : A ⊸ ◇ₖA` dari bagian 11 proposal.
- `await` membaca `await : ◇ₖA ⊸ A`: ◇ₖA di konteks boleh dipakai sebagai A.
- `cancel` membaca `cancel : ◇ₖA ⊸ ◇ₖA`. Premis dan kesimpulannya sama: cancel
  tidak menghasilkan A dan tidak menghapus ◇ₖA dari konteks. Secara
  derivabilitas aturan ini tidak menambah teorema; isinya baru muncul di term
  assignment (tahap berikutnya), sebagai aksi protocol.
- Grade `k` belum dipakai oleh aturan mana pun: `submit`, `await`, dan
  `cancel` berlaku untuk setiap `k` dan tidak mengubahnya.
- `free : A ⊸ 1` dari proposal bukan aturan logika. Di `Examples.v` ia muncul
  sebagai hipotesis `buf ⊸ 1` di konteks.

## Teorema tentang aturan (bukan aturan)

| Nama | Pernyataan | File |
|------|------------|------|
| `identity` | `A ⊢ A` untuk setiap A (dengan `aw = true`) | `Identity.v` |
| `cut_admissible` | bila `Δ₁ ⊢ A` dan `Γ ⊢ C` dengan Γ permutasi dari `A, Δ₂`, maka `Δ₁, Δ₂ ⊢ C` (untuk setiap `aw`) | `CutElim.v` |
