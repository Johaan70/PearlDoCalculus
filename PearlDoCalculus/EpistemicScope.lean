/-
Copyright (c) 2026 Johan. Released under Apache 2.0 license.
Authors: Johan, Claude
-/
import PearlDoCalculus.DAG
import PearlDoCalculus.CausalModel
import PearlDoCalculus.DSeparation

/-!
# Epistemisk rekkevidde

Denne modulen inneholder ingen bevis om kausale forhold. Den finnes for å
gjøre eksplisitt, inne i det formelle systemet selv, hvor grensen går
mellom det biblioteket *etablerer* og det biblioteket *forutsetter*.

## Skillet

**Deduktivt innhold — det Lean verifiserer.** Gitt en `DAG G` og en
`CausalModel G α`, følger justeringsformlene nødvendig av modellens
struktur. `frontdoor_adjustment_observable` er verifisert sorry-fri, og
`#print axioms` viser bare `propext`, `Classical.choice`, `Quot.sound`.
Dette er et resultat om et formelt kalkyle, på linje med ethvert annet
verifisert inferenssystem.

**Utenomsystemisk innhold — det Lean ikke kan verifisere, heller ikke i
prinsippet.** Om en gitt `DAG G` er den korrekte representasjonen av et
empirisk fenomen. Dette omfatter: om kantrelasjonen svarer til faktiske
kausalmekanismer, om alle felles årsaker er med blant nodene, om
variabelinndelingen er den rette, og om intervensjon slik den er
formalisert her — trunkert faktorisering — er riktig semantikk for det
kausale spørsmålet som stilles.

Collingwoods poeng, transponert: å verifisere et bevis re-enakterer
*logikken* i en slutning fra dens premisser. Det re-enakterer ikke, og kan
ikke re-enaktere, den *dømmekraften* som avgjorde at premissene gjelder i
en gitt situasjon. Den dømmekraften er empirisk, historisk og reviderbar
på måter et sorry-fritt Lean-bevis ikke er.

## Hva denne modulen gjør

Den navngir forutsetningene og gir dem et sted å bo i signaturen, slik at
ingen lemma i biblioteket kan siteres uten at det også siteres hva det
forutsatte.

Statusmerkingen står i dokumentasjonen, ikke i typen. Det er med hensikt:
en forutsetnings epistemiske status har ikke logisk innhold, og å legge
den inn i typen ville antydet at Lean kan sjekke den.
-/

namespace PearlDoCalculus.EpistemicScope

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ## 1. Forutsetninger som navngitte objekter

Framfor å la antakelser som «ingen umålte konfundere» leve implisitt inne
i en hypotese uten videre kommentar, navngir vi hver tilbakevendende
forutsetning. Det gir ingen deduktiv kraft. Det gir et sted å feste den
epistemiske statusen, og tvinger ethvert teorem som bruker en av dem til
å si det i signaturen framfor i prosa.
-/

/--
**Grafen svarer til fenomenet.** At kantrelasjonen i `G` faktisk
representerer de kausale mekanismene i systemet som studeres.

*Status: empirisk.* Ingen graf-intern sjekk sertifiserer dette. Det er en
substansiell påstand om verden, begrunnet — om i det hele tatt — ved
eksperiment, fagkunnskap eller argument fra bakgrunnsvitenskap.

Feltet er `True` fordi det ikke finnes noe å fylle inn. Det er ikke en
plassholder for et framtidig bevis.
-/
structure GraphFaithfulToPhenomenon (G : DAG V) : Prop where
  assumed : True

/--
**Kausal tilstrekkelighet.** At enhver felles årsak til to eller flere
variabler i `V` selv ligger i `V` — altså ingen umålt konfundering.

Dette er den mest konsekvensrike forutsetningen bak
identifikasjonsresultater som front-door og back-door.

*Status: empirisk, og i streng forstand ufalsifiserbar fra observasjonelle
data alene.* Begrunnelsen ligger alltid utenfor grafen: studiedesign,
fagkunnskap om hva som faktisk ble målt.

Merk: `FrontDoorModel` i `FrontDoor.lean` koder en *bestemt* konfunderende
struktur i typen — `U` påvirker både `X` og `Y`. Det er en styrke ved den
konstruksjonen: konfunderingen er eksplisitt, ikke bortantatt. Men at den
strukturen er den *riktige* for et gitt fenomen, forblir empirisk.
-/
structure CausalSufficiency (G : DAG V) : Prop where
  assumed : True

/--
**Intervensjonssemantikk.** At `do(X = x)` som trunkert faktorisering —
å erstatte `pX_given_U` med punktmasse — er riktig formalisering av det
kausale spørsmålet.

*Status: konvensjonell.* Dette er ikke sant eller usant, men et valg med
konsekvenser. Andre intervensjonsbegreper finnes (myke intervensjoner,
politikk-intervensjoner betinget av observerte variabler), og de gir andre
identifikasjonsresultater.
-/
structure InterventionSemantics (G : DAG V) : Prop where
  assumed : True

/--
**Variabelinndeling.** Valget av å representere verteksmengden med
`[DecidableEq V]` og `[Fintype V]`.

*Status: konvensjonell.* Det er en beslutning om hvordan variabler
individueres i formalismen, tatt av bevistekniske grunner — `Finset` og
avgjørbare grafoperasjoner. Den er ikke nøytral: den forutsetter at
variabelidentitet alltid er avgjørbar, og at verteksmengden er endelig.

Dette er svaret på spørsmålet Zixiao Jolene Wang stilte i `#Statlib` på
Zulip om hvorfor `DecidableEq V` sitter på strukturnivå. Det ærlige svaret
er at det kom av `Finset`-representasjonen framfor av et prinsipielt valg
— og at det derfor bør dokumenteres som en modelleringsbeslutning, ikke
som en teknisk fotnote.

Konsekvensen er reell: biblioteket kan ikke uttrykke kausale modeller over
kontinuerlige eller uendelige variabelrom uten en annen representasjon.
-/
structure VariableIndividuation : Prop where
  assumed : True

/--
**Endelig diskret verdirom.** At hver `α v` er en `Fintype` med
`DecidableEq`, som `CausalModel`-strukturen krever.

*Status: konvensjonell.* Målteoretisk kausalitet med kontinuerlige
variabler krever et annet fundament enn `PMF` over endelige typer. Det er
ikke en svakhet ved resultatene, men en avgrensning av hva de gjelder for.
-/
structure FiniteDiscreteValues (α : V → Type v) : Prop where
  assumed : True

/-! ## 2. Rekkevidden til et teorem, gjort eksplisitt i signaturen

Mønsteret under er den konkrete leveransen: ethvert
identifikasjonsteorem i dette biblioteket bør kunne pakkes i denne formen,
slik at det å lese *signaturen* — uten README eller artikkel — allerede
forteller hva slags påstand som framsettes.
-/

/--
Et identifikasjonsresultat med rekkevidden festet til seg: det deduktive
innholdet `claim`, sammen med de empiriske og konvensjonelle
forutsetningene det hviler på, gjort til argumenter framfor prosakontekst.

`frontdoor_adjustment_observable` kan pakkes som en instans av denne. Det
deduktive innholdet forblir nøyaktig like sterkt som det allerede er. Det
som endres, er at forutsetningene blir synlige i typen framfor å måtte
utledes av den som siterer resultatet.
-/
structure ScopedResult (G : DAG V) (α : V → Type v) (claim : Prop) where
  /-- Det Lean faktisk verifiserer. -/
  deductive_content : claim
  /-- At grafen svarer til fenomenet. Empirisk. -/
  graph_faithful : GraphFaithfulToPhenomenon G
  /-- At alle felles årsaker er med. Empirisk. -/
  sufficiency : CausalSufficiency G
  /-- At trunkert faktorisering er riktig intervensjonsbegrep. Konvensjonell. -/
  intervention : InterventionSemantics G
  /-- At variabelindividuering med `DecidableEq` er adekvat. Konvensjonell. -/
  individuation : VariableIndividuation
  /-- At endelige diskrete verdirom er adekvat. Konvensjonell. -/
  finite_values : FiniteDiscreteValues α
  /--
  Fritekstpeker til den empiriske begrunnelsen, om noen, for
  forutsetningene over i den konkrete anvendelsen resultatet brukes i.
  Med hensikt ikke maskinsjekkbar — det er hele poenget.
  -/
  empirical_note : String := ""

/-! ## 3. Hva denne modulen ikke kan gjøre

Dette står som kommentar fordi det ikke kan stå som teorem.

**Ingen definisjon her kan verifisere at forutsetningene holder for noen
faktisk variabelmengde.** `assumed : True` er ikke en plassholder for et
framtidig bevis — det finnes ikke noe bevis å fylle inn. Dette er
empiriske påstander om kausal struktur i verden, sjekkbare (om i det hele
tatt) bare ved eksperiment, fagkunnskap eller argument utenfor formalismen.

**`ScopedResult` gjør ingen lemma «mer sant».** Den gjør *bruksvilkårene*
for et allerede sant lemma lesbare på brukspunktet. Den deduktive
garantien var alltid nøyaktig så sterk som `frontdoor_adjustment_observable`
beviser. Det som manglet, var en strukturell påminnelse, synlig i typen,
om at garantien er betinget.

**Dette er ikke en reservasjon mot verdien av de sorry-frie resultatene.**
Et sunt kalkyle for identifikasjon gitt en graf er et genuint resultat.
Hensikten her er smalere: å hindre at resultatet leses, av bibliotekets
egne brukere, som en avgjørelse av et spørsmål det ikke avgjør.

**Merk også hva som gjenstår internt.** `DSepSoundSkeleton.lean` har
fortsatt åpne `sorry`. Ethvert resultat som avhenger av dem, er ikke
verifisert — og `#print axioms` er verktøyet som avgjør det, ikke denne
modulen.
-/

end PearlDoCalculus.EpistemicScope
