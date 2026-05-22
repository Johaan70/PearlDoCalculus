# PearlDoCalculus

Formalisering av Judea Pearls do-kalkyle i Lean 4, bygget på Mathlib.

## Status

**Milepæl 1 — Minimal back-door-justering** ✓ `SimpleConfounder.lean`.
Trekanten `Z → X`, `Z → Y`, `X → Y`; back-door-formelen bevist uten `sorry`.

**Milepæl 2a — Front-door, strukturell form** ✓ `FrontDoor.lean`.
Strukturen `U → X`, `U → Y`, `X → Z`, `Z → Y` med `U` uobservert. To teoremer:
`frontdoor_structural` (intervensjon propagert gjennom mediator) og
`frontdoor_X_cancellation` (den algebraiske kjernen som eliminerer `U`-referansen).

Alle teoremer hviler kun på Mathlibs tre standardaksiomer
(`propext`, `Classical.choice`, `Quot.sound`).

## Bygging på dropletten

```bash
# 1. Klon prosjektet til dropletten
cd ~
git clone <repo> PearlDoCalculus     # eller rsync mappen fra lokal
cd PearlDoCalculus

# 2. Hent gjeldende Lean-toolchain fra Mathlib master
#    (sikrer kompatibilitet med dagens Mathlib)
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain \
     -o lean-toolchain

# 3. Initialiser og hent Mathlib-cache (sparer flere timers kompilering)
lake update
lake exe cache get

# 4. Bygg
lake build
```

Hvis `elan` mangler:
```bash
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh | bash
source ~/.profile
```

Mathlib-cachen er på rundt 7–10 GB. Selve bygget av `PearlDoCalculus` er
sekunder når Mathlib er på plass.

## Filstruktur

```
PearlDoCalculus/
├── lakefile.lean                       # byggekonfigurasjon
├── lean-toolchain                      # Lean-versjon (oppdater via curl)
├── PearlDoCalculus.lean                # toppnivå-import
└── PearlDoCalculus/
    ├── SimpleConfounder.lean           # MILEPÆL 1 — fullført
    └── DAG.lean                        # skjelett for milepæl 2+
```

## Roadmap

**Milepæl 1** ✓ Minimal konfundermodell + back-door-justering for trekanten.

**Milepæl 2** Generelle endelige DAG-er
- Foreldre-, etterkommer-, forfedrefunksjoner (delvis i `DAG.lean`)
- Faktorisering av fellesfordeling iht. DAG
- Trunkert faktorisering = intervensjon

**Milepæl 3** d-separasjon
- Induktiv definisjon av stier
- Chain/fork/collider-blokkering
- Korrekthetsteorem: d-separasjon ⇒ betinget uavhengighet

**Milepæl 4** Generelt back-door-kriterium og generell back-door-justering
- Definisjon av kriteriet
- Hovedteorem (Pearl 1995)

**Milepæl 5** De tre reglene i do-kalkylen
- Regel 1 (innsetting/sletting av observasjon)
- Regel 2 (utveksling av observasjon med intervensjon)
- Regel 3 (innsetting/sletting av intervensjon)

**Milepæl 6** Shpitser–Pearl-fullstendighet (2006)
- ID-algoritmen
- Hvis identifikasjon er mulig, finnes derivasjon i do-kalkylen
- Dette er langt løp — sannsynligvis flere måneders arbeid

## Designvalg

* **PMF i stedet for generelle målerom**: `PMF` (sannsynlighetsmassefunksjoner)
  gir ren syntaks for diskrete fordelinger og er nok for den endelige
  DAG-teorien. Kontinuerlige utvidelser kan komme senere via
  `MeasureTheory.ProbabilityMeasure`.

* **Acyklicitet via rangfunksjon**: For endelige grafer er en topologisk
  sortering ekvivalent med fravær av sykluser, og er langt lettere å
  arbeide med formelt enn induktiv stilukking.

* **Strukturell semantikk**: Modellen er gitt ved en `structure` med kjerner
  hvis signatur koder DAG-en. Dette er Pearls strukturelle ligningsmodell-
  perspektiv direkte oversatt til Lean-typene.

## Hvorfor dette prosjektet

Skillet mellom `P(Y | X)` (betinging på observasjon) og `P(Y | do(X))`
(intervensjon) er filosofisk det viktigste i moderne kausal inferens —
og det er ingenting i Mathlib som vet at de er forskjellige. Denne
formaliseringen tegner den grensen presist.
