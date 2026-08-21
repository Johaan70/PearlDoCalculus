# PearlDoCalculus

Formalisering av Judea Pearls do-kalkyle i Lean 4, bygget på Mathlib.

## Status

**Milepæl 1 — Minimal back-door-justering** ✓ `SimpleConfounder.lean`.
Trekanten `Z → X`, `Z → Y`, `X → Y`; back-door-formelen bevist uten `sorry`.

**Milepæl 2a — Front-door, strukturell form** ✓ `FrontDoor.lean`.
Strukturen `U → X`, `U → Y`, `X → Z`, `Z → Y` med `U` uobservert. To teoremer:
`frontdoor_structural` (intervensjon propagert gjennom mediator) og
`frontdoor_X_cancellation` (den algebraiske kjernen som eliminerer `U`-referansen).
**Milepæl 2b — Front-door, observerbar form** ✓ `FrontDoorObservable.lean`.
`frontdoor_adjustment_observable`: kausaleffekten uttrykt utelukkende i
observerbare størrelser, P(y | do(x)) = Σ_z P(z|x) Σ_x' P(x') P(y|x',z).
Den uobserverte konfunderen U opptrer ikke i konklusjonen.
**Ikke-vakuøsitet** ✓ `verification/Check5.lean`. En eksplisitt firenoders
modell over `Bool` med ekte konfundering, der
`frontdoor_adjustment_observable` faktisk anvendes. Teoremet har innhold,
ikke bare en oppfyllbar signatur.

**Milepæl 3 — d-separasjon, grafdelen** ✓ `DSepSoundSkeleton.lean`.
`moral_walk_of_open`: fra en åpen vandring i `G` til en moralvandring som
unngår `Z` internt, med kollidere håndtert via ekteskapskanter.
`dsep_of_moral_sep`: separasjon i moralgrafen gir d-separasjon i `G`.
Hele den grafteoretiske halvdelen av Lauritzen-ruten.

**Milepæl 3b — faktorisering** ✓ `condIndep_of_product_form`. Faktoriserer
fellesfordelingen i to deler langs en separator og utleder `CondIndep`.
Krever at `X`, `Y`, `Z` er parvis disjunkte — uten det dobbelttelles
overlappet.

**Aksiomsjekk.** Sju resultater verifisert i `verification/AxiomCheck.lean`,
alle med bare `propext`, `Classical.choice`, `Quot.sound`. Ingen `sorryAx`.

## Åpent

Tre `sorry` gjenstår i `DSepSoundSkeleton.lean`. Ingen av de beviste
resultatene hviler på dem — `#print axioms` bekrefter det.

To av dem deler samme underliggende mangel: `joint_splits` og
`marginal_eq_restricted_joint` trenger begge at `jointUpTo` faktoriserer
som et produkt over noder. `jointUpTo` er bygget som en `PMF.bind`-kjede
over rangnivåer med `cast` langs mengdelikheter i hvert steg, og det finnes
ingen lemmaer om `extendOverList`. Det lemmaet er den ene tingen som låser
opp begge.

Det tredje, `dsep_sound'`, er sammensetningen og blir kort når de to andre
står.

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
