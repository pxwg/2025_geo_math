// Packages
#import "@preview/physica:0.9.5": *
#import "@preview/commute:0.3.0": arr, commutative-diagram, node
#import "@preview/catppuccin:1.0.0": catppuccin, flavors

// colors controled by the `colored` variable passed in the command line or by default
// which is `false` and help to manage the default (preview in url) and uncolored (published in pdf) version
// TODO: become a package to be used in other documents

// Get the `colored` variable from the command line input
// Then determine the color scheme based on the `colored` variable
#let coloreds = sys.inputs
#let get_input(input_dict) = {
  for (key, value) in input_dict {
    if key == "colored" {
      return value
    }
  }
  return true
}

#let colored = get_input(coloreds)

#let get_color_scheme(input_value) = {
  if input_value == "false" {
    (
      background: catppuccin.with(flavors.latte),
      flavors: flavors.latte,
    )
  } else {
    (
      background: catppuccin.with(flavors.mocha),
      flavors: flavors.mocha,
    )
  }
}
#let showed_flavors(colored) = {
  if colored == "false" {
    flavors.latte
  } else {
    flavors.mocha
  }
}

#let color_scheme = get_color_scheme(colored).background
#let color_flavors = get_color_scheme(colored).flavors
#show: color_scheme

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
      #if name != none [*Example* (#emph(name))] else [*Example*]
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

#let proposition(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.green.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Proportion* (#emph(name))] else [*Proportion*]
      #body
    ],
  )
}

#let remark(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.flamingo.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Remark* (#emph(name))] else [*Remark*]
      #body
    ],
  )
}


#let proof(name: none, body) = {
  block(
    stroke: 1pt + rgb(color_flavors.colors.lavender.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
  )[
    #if name != none [_Proof_. (#emph(name)). ] else [_Proof_. ]
    #body
    #h(1fr)
    $qed$
  ]
}
