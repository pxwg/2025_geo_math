#let colored = sys.inputs.keys()

// Packages
#import "@preview/physica:0.9.5": *
// #import "../preamble.typ"
// colors controled by the `colored` variable passed in the command line or by default
// which is `false` and help to manage the default (preview in url) and uncolored (published in pdf) version
// TODO: better false (pdf) color flavors to contral definition block etc.
// TODO: become a package to be used in other documents
#import "@preview/catppuccin:1.0.0": catppuccin, flavors
#let color_flavors = flavors.mocha
#let flavor(colored, color_flavors) = {
  if colored == "false" {
    catppuccin.with(flavors.lattie)
  } else { catppuccin.with(color_flavors) }
}

// #show: catppuccin.with(color_flavors)
#show: flavor(colored, color_flavors)

// ### Example:
// ```typst
// #definition(name: 'prefactorization algebra',[
//   A prefactorization algebra $cal(F)$ on $M$ would assign to each open subset $U$ with a vector space $cal(F)$, together with a maps
//   $
//     m_V^(U_1, U_2, dots, U_n): cal(F)(U_1) times.circle cal(F)(U_2) times.circle dots times.circle cal(F)(U_n) --> cal(F)(V),
//   $
// ])
// ```
#let definition(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.blue.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Definition* (#emph(name))] else [*Definition*]
      #body
    ],
  )
}
#let example(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.maroon.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*example* (#emph(name))] else [*example*]
      #body
    ],
  )
}
#let theorem(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.peach.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Theorem* (#emph(name))] else [*Theorem*]
      #body
    ],
  )
}
