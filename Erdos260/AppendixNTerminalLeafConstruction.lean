import Mathlib
import Erdos260.GlobalCarryShellAssembly
import Erdos260.ShellPaidChernoffConstruction
import Erdos260.Constants

/-!
# N.3.3 terminal separated leaf construction
-/

namespace Erdos260

open Finset Real

noncomputable section

/--
Faithful proof-v4 N.3.3 route: a real table-routed terminal family, terminal
mass domination, and all five non-drop class estimates assemble directly into
the separated terminal leaf.
-/
def classicalTerminalN33SeparatedLeafFromClosedN33
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bdd :
      @TableRoutedBddClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  ClassicalTerminalN33SeparatedLeafData.ofClosedN33
    E row supp thr terminalWeight terminalMass densePack progress endpoint cnl bdd

/-- Faithful proof-v4 N.3.3 route with the five non-drop class estimates already
bundled.  This matches the aggregate terminal-routing table form while still
projecting to the separated leaf consumed by the final endpoint. -/
def classicalTerminalN33SeparatedLeafFromClosedN33Bundled
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (classBounds :
      @TableRoutedTerminalFiveClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D O_P O_E O_CNL O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  ClassicalTerminalN33SeparatedLeafData.ofClosedN33
    E row supp thr terminalWeight terminalMass
    classBounds.densePack classBounds.progress classBounds.endpoint
    classBounds.cnl classBounds.bdd

/-- Faithful proof-v4 N.3.3 route when terminal mass has already been grouped
by output object and each grouped charge is compressed by Lemma N.3.1. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassClosedN33
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bdd :
      @TableRoutedBddClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTerminalN33SeparatedLeafFromClosedN33
    E row supp thr terminalWeight
    terminalMass.toTableRoutedTerminalMassInputData
    densePack progress endpoint cnl bdd

/-- Faithful N.3.3 route from grouped N.3.1 terminal compression and the
proof-v4 L.1.2/G.35 CNL Kraft explanation for the clean-CNL class. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassCNLKraftClosedN33
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {shell : FailingDyadicShell} {cStar xi : Real}
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bdd :
      @TableRoutedBddClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTerminalN33SeparatedLeafFromCompressedMassClosedN33
    E row supp thr terminalWeight terminalMass
    densePack progress endpoint cnl.toTableRoutedCNLClassInputData bdd

/-- Package the proof-v4 N.3.3 terminal-mass input and bundled five-class
estimate into the canonical table-routed terminal absorption record used by the
N.24 provider. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33Bundled
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (classBounds :
      @TableRoutedTerminalFiveClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D O_P O_E O_CNL O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData.ofClosedN33
    E row supp thr terminalWeight
    { hterm := terminalMass.hterm
      hD := classBounds.densePack.hD
      hP := classBounds.progress.hP
      hE := classBounds.endpoint.hE
      hCNL := classBounds.cnl.hCNL
      hBdd := classBounds.bdd.hBdd }

/-- Package the fully separated proof-v4 N.3.3 terminal-mass and five class
estimates into the canonical table-routed terminal absorption record used by
the N.24 provider. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bdd :
      @TableRoutedBddClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33Bundled
    E row supp thr terminalWeight terminalMass
    { densePack := densePack
      progress := progress
      endpoint := endpoint
      cnl := cnl
      bdd := bdd }

/-- Package the N.3.3 terminal absorption data when terminal mass is supplied
through grouped per-output N.3.1 compression. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassClosedN33
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bdd :
      @TableRoutedBddClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33
    E row supp thr terminalWeight
    terminalMass.toTableRoutedTerminalMassInputData
    densePack progress endpoint cnl bdd

/-- Package N.3.3 terminal absorption from grouped N.3.1 terminal compression
and the proof-v4 L.1.2/G.35 CNL Kraft explanation for the clean-CNL class. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassCNLKraftClosedN33
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {shell : FailingDyadicShell} {cStar xi : Real}
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bdd :
      @TableRoutedBddClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassClosedN33
    E row supp thr terminalWeight terminalMass
    densePack progress endpoint cnl.toTableRoutedCNLClassInputData bdd

/-- Package the fully separated proof-v4 N.3.3 terminal data when the bounded
class is supplied directly by the L.6-backed N.3.2 certificate. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33BddL6
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bddL6 :
      ShellPaidBddClassBoundData leaf
        (AppendixN.classMassV4
          ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) inferInstance E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega }))
          terminalWeight OutputClassV4.bdd)
        O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq sigma := Classical.decEq sigma
  exact {
    sigma := sigma
    iota := iota
    linIota := inferInstance
    E := E
    row := row
    supp := supp
    thr := thr
    terminalWeight := terminalWeight
    terminalMass := terminalMass
    densePack := densePack
    progress := progress
    endpoint := endpoint
    cnl := cnl
    bddL6 := bddL6 }

/-- Package the fully separated proof-v4 N.3.3 terminal data when the bounded
class is supplied in the literal L.6.1/L.6.2/L.6.3 low/paid split form. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33BddL6
    E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
    (ShellPaidBddClassBoundData.fromLowPaidSplit bddLowPaid)

/-- Package the fully separated proof-v4 N.3.3 terminal data when the bounded
class is supplied in the finite-overlap form of L.6.2 before it is collapsed to
the literal L.6.1/L.6.2/L.6.3 low/paid split. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33LowPaid
    E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
    bddFiniteOverlap.toLowPaidSplitData

/-- Package N.3.3 terminal absorption from grouped N.3.1 terminal compression,
the proof-v4 L.1.2/G.35 CNL Kraft explanation, and the literal L.6 low/paid
split for the bounded class. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassCNLKraftClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33LowPaid
    E row supp thr terminalWeight
    terminalMass.toTableRoutedTerminalMassInputData
    densePack progress endpoint cnl.toTableRoutedCNLClassInputData bddLowPaid

/-- Package N.3.3 terminal absorption from grouped N.3.1 terminal compression,
the L.1.2/G.35 CNL Kraft explanation, and the finite-overlap L.6.2 form of
the bounded-class low/paid split. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassCNLKraftClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassCNLKraftClosedN33LowPaid
    E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
    bddFiniteOverlap.toLowPaidSplitData

/-- Package N.3.3 terminal absorption from grouped N.3.1 terminal compression,
DensePack support injection, the proof-v4 L.1.2/G.35 CNL Kraft explanation, and
the literal L.6 low/paid split for the bounded class. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportCNLKraftClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassCNLKraftClosedN33LowPaid
    E row supp thr terminalWeight terminalMass
    densePack.toTableRoutedDensePackClassInputData
    progress endpoint cnl bddLowPaid

/-- Package N.3.3 terminal absorption from grouped N.3.1 compression,
DensePack support injection, CNL Kraft data, and a finite-overlap L.6.2
bounded-class split. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportCNLKraftClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportCNLKraftClosedN33LowPaid
    E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
    bddFiniteOverlap.toLowPaidSplitData

/-- Package N.3.3 terminal absorption from grouped N.3.1 terminal compression,
DensePack support injection, Chernoff high-cost progress injection, the
proof-v4 L.1.2/G.35 CNL Kraft explanation, and the literal L.6 low/paid split
for the bounded class. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffCNLKraftClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassChernoffInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportCNLKraftClosedN33LowPaid
    E row supp thr terminalWeight terminalMass densePack
    progress.toTableRoutedProgressClassInputData endpoint cnl bddLowPaid

/-- Package N.3.3 terminal absorption from grouped N.3.1 compression,
DensePack support, Chernoff progress, CNL Kraft data, and a finite-overlap L.6.2
bounded-class split. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffCNLKraftClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassChernoffInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffCNLKraftClosedN33LowPaid
    E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
    bddFiniteOverlap.toLowPaidSplitData

/-- Package N.3.3 terminal absorption from grouped N.3.1 terminal compression,
DensePack support injection, Chernoff high-cost progress injection,
Return/OLC endpoint leakage, the proof-v4 L.1.2/G.35 CNL Kraft explanation,
and the literal L.6 low/paid split for the bounded class. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffEndpointReturnCNLKraftClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassChernoffInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_P)
    (endpoint :
      @TableRoutedEndpointClassReturnInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffCNLKraftClosedN33LowPaid
    E row supp thr terminalWeight terminalMass densePack progress
    endpoint.toTableRoutedEndpointClassInputData cnl bddLowPaid

/-- Package N.3.3 terminal absorption from the full manuscript provider stack
through Return/OLC endpoint leakage, with the bounded class supplied in the
finite-overlap L.6.2 form. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffEndpointReturnCNLKraftClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassChernoffInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_P)
    (endpoint :
      @TableRoutedEndpointClassReturnInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffEndpointReturnCNLKraftClosedN33LowPaid
    E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
    bddFiniteOverlap.toLowPaidSplitData

/-- Raw proof-v4 N.3.3 route: package the terminal table directly from the
displayed terminal-mass and four non-bounded class inequalities, with the
bounded class supplied by the literal L.6 low/paid split. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromRawClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (hterm :
      termMass <=
        Finset.sum
          ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) inferInstance E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega }))
          terminalWeight)
    (hD :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.densePack <= O_D)
    (hP :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.progress <= O_P)
    (hE :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.endpoint <= O_E)
    (hCNL :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.cnl <= O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  letI : DecidableEq sigma := Classical.decEq sigma
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33LowPaid
    E row supp thr terminalWeight
    { hterm := hterm }
    { hD := hD }
    { hP := hP }
    { hE := hE }
    { hCNL := hCNL }
    bddLowPaid

/-- Raw proof-v4 N.3.3 route with the bounded class supplied at the
finite-overlap L.6.2 boundary before collapsing to the standard low/paid
split. -/
def classicalTableRoutedDirectFiveClassTerminalAbsorptionFromRawClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (hterm :
      termMass <=
        Finset.sum
          ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) inferInstance E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega }))
          terminalWeight)
    (hD :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.densePack <= O_D)
    (hP :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.progress <= O_P)
    (hE :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.endpoint <= O_E)
    (hCNL :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.cnl <= O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTableRoutedDirectFiveClassTerminalAbsorptionFromRawClosedN33LowPaid
    E row supp thr terminalWeight hterm hD hP hE hCNL
    bddFiniteOverlap.toLowPaidSplitData

/-- Faithful proof-v4 N.3.3 route from the internally-decidable table-routed
terminal absorption package used by the N.24 canonical-Y interface. -/
def classicalTerminalN33SeparatedLeafFromTableRoutedDirect
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := Classical.decEq data.sigma
  letI : LinearOrder data.iota := data.linIota
  exact {
    sigma := data.sigma
    iota := data.iota
    linIota := data.linIota
    E := data.E
    row := data.row
    supp := data.supp
    thr := data.thr
    terminalWeight := data.terminalWeight
    terminalMass := data.terminalMass
    densePack := data.classBounds.densePack
    progress := data.classBounds.progress
    endpoint := data.classBounds.endpoint
    cnl := data.classBounds.cnl
    bdd := data.classBounds.bdd }

/-- Faithful proof-v4 N.3.3 route from the table-routed terminal package whose
bounded class is explicitly backed by the L.6 corrected-residual/shell-paid
Chernoff bridge. -/
def classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
        leaf termMass O_D O_P O_E O_CNL O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirect
    data.toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

/-- Direct separated N.3.3 leaf from the proof-v4 terminal table and literal
L.6 low/paid split for the bounded class. -/
def classicalTerminalN33SeparatedLeafFromClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33LowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddLowPaid)

/-- Direct separated N.3.3 leaf whose bounded class is supplied at the
finite-overlap L.6.2 boundary before collapsing to the standard low/paid split. -/
def classicalTerminalN33SeparatedLeafFromClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromClosedN33FiniteOverlapLowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddFiniteOverlap)

/-- Direct separated N.3.3 leaf from grouped N.3.1 terminal compression, the
proof-v4 L.1.2/G.35 CNL Kraft explanation, and the literal L.6 low/paid split
for the bounded class. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassCNLKraftClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassCNLKraftClosedN33LowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddLowPaid)

/-- Direct separated N.3.3 leaf from grouped N.3.1 terminal compression, CNL
Kraft data, and the finite-overlap L.6.2 bounded-class split. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassCNLKraftClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassCNLKraftClosedN33FiniteOverlapLowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddFiniteOverlap)

/-- Direct separated N.3.3 leaf from grouped N.3.1 terminal compression,
DensePack support injection, the proof-v4 L.1.2/G.35 CNL Kraft explanation, and
the literal L.6 low/paid split for the bounded class. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassDensePackSupportCNLKraftClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportCNLKraftClosedN33LowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddLowPaid)

/-- Direct separated N.3.3 leaf from grouped N.3.1 compression, DensePack
support, CNL Kraft data, and a finite-overlap L.6.2 bounded-class split. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassDensePackSupportCNLKraftClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportCNLKraftClosedN33FiniteOverlapLowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddFiniteOverlap)

/-- Direct separated N.3.3 leaf from grouped N.3.1 terminal compression,
DensePack support injection, Chernoff high-cost progress injection, the
proof-v4 L.1.2/G.35 CNL Kraft explanation, and the literal L.6 low/paid split
for the bounded class. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassDensePackSupportProgressChernoffCNLKraftClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassChernoffInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffCNLKraftClosedN33LowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddLowPaid)

/-- Direct separated N.3.3 leaf from grouped N.3.1 compression, DensePack
support, Chernoff progress, CNL Kraft data, and a finite-overlap L.6.2
bounded-class split. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassDensePackSupportProgressChernoffCNLKraftClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassChernoffInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffCNLKraftClosedN33FiniteOverlapLowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddFiniteOverlap)

/-- Direct separated N.3.3 leaf from grouped N.3.1 terminal compression,
DensePack support injection, Chernoff high-cost progress injection,
Return/OLC endpoint leakage, the proof-v4 L.1.2/G.35 CNL Kraft explanation,
and the literal L.6 low/paid split for the bounded class. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassDensePackSupportProgressChernoffEndpointReturnCNLKraftClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassChernoffInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_P)
    (endpoint :
      @TableRoutedEndpointClassReturnInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffEndpointReturnCNLKraftClosedN33LowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddLowPaid)

/-- Direct separated N.3.3 leaf from the full manuscript provider stack through
Return/OLC endpoint leakage, with the bounded class supplied in finite-overlap
L.6.2 form. -/
def classicalTerminalN33SeparatedLeafFromCompressedMassDensePackSupportProgressChernoffEndpointReturnCNLKraftClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {shell : FailingDyadicShell}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassCompressionInputData sigma iota
        (Classical.decEq sigma) inferInstance E row supp thr terminalWeight
        termMass)
    (densePack :
      @TableRoutedDensePackClassSupportInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_D)
    (progress :
      @TableRoutedProgressClassChernoffInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_P)
    (endpoint :
      @TableRoutedEndpointClassReturnInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight cStar xi X O_E)
    (cnl :
      @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight shell cStar xi O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffEndpointReturnCNLKraftClosedN33FiniteOverlapLowPaid
      E row supp thr terminalWeight terminalMass densePack progress endpoint cnl
      bddFiniteOverlap)

/-- Raw proof-v4 N.3.3 separated leaf from terminal/class inequalities and the
literal L.6 low/paid split for the bounded class. -/
def classicalTerminalN33SeparatedLeafFromRawClosedN33LowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (hterm :
      termMass <=
        Finset.sum
          ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) inferInstance E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega }))
          terminalWeight)
    (hD :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.densePack <= O_D)
    (hP :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.progress <= O_P)
    (hE :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.endpoint <= O_E)
    (hCNL :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.cnl <= O_CNL)
    (bddLowPaid :
      ShellPaidBddClassBoundData.LowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromRawClosedN33LowPaid
      E row supp thr terminalWeight hterm hD hP hE hCNL bddLowPaid)

/-- Raw separated N.3.3 leaf with the bounded class supplied at the
finite-overlap L.6.2 boundary before collapsing to the standard low/paid split. -/
def classicalTerminalN33SeparatedLeafFromRawClosedN33FiniteOverlapLowPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (hterm :
      termMass <=
        Finset.sum
          ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) inferInstance E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega }))
          terminalWeight)
    (hD :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.densePack <= O_D)
    (hP :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.progress <= O_P)
    (hE :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.endpoint <= O_E)
    (hCNL :
      AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.cnl <= O_CNL)
    (bddFiniteOverlap :
      ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) inferInstance E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd :=
  classicalTerminalN33SeparatedLeafFromTableRoutedDirectBddL6
    (classicalTableRoutedDirectFiveClassTerminalAbsorptionFromRawClosedN33FiniteOverlapLowPaid
      E row supp thr terminalWeight hterm hD hP hE hCNL bddFiniteOverlap)

/-- Remaining proof-v4 data still needed before a no-input N.3.3 terminal leaf
provider can be installed. -/
def classicalTerminalN33SeparatedLeafOpenItems : List String :=
  [ "N.1.0 concrete same-threshold output events and residual-multiplier comparison for the terminal table",
    "N.3.1 grouped terminal compression over routed output objects",
    "N.3.3 DensePack support injection and unit-weight alignment",
    "N.3.3 Chernoff high-cost progress injection and weight domination",
    "N.3.3 Return/OLC endpoint leakage alignment and return-piece nonnegativity",
    "N.3.3 clean-CNL class alignment to the L.1.2/G.35 Kraft leaf",
    "N.3.3 L.6 low/paid bounded-dirty-return split" ]

theorem classicalTerminalN33SeparatedLeafOpenItems_nonempty :
    classicalTerminalN33SeparatedLeafOpenItems = [] -> False := by
  intro h
  simp [classicalTerminalN33SeparatedLeafOpenItems] at h

theorem classicalTerminalN33SeparatedLeafOpenItems_length :
    classicalTerminalN33SeparatedLeafOpenItems.length = 7 := by
  rfl

theorem classicalTerminalN33SeparatedLeafOpenItems_eq :
    classicalTerminalN33SeparatedLeafOpenItems =
      [ "N.1.0 concrete same-threshold output events and residual-multiplier comparison for the terminal table",
        "N.3.1 grouped terminal compression over routed output objects",
        "N.3.3 DensePack support injection and unit-weight alignment",
        "N.3.3 Chernoff high-cost progress injection and weight domination",
        "N.3.3 Return/OLC endpoint leakage alignment and return-piece nonnegativity",
        "N.3.3 clean-CNL class alignment to the L.1.2/G.35 Kraft leaf",
        "N.3.3 L.6 low/paid bounded-dirty-return split" ] := by
  rfl

end

end Erdos260
