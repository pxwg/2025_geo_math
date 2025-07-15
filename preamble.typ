// Complied by: `typst --input colored=false --input preview=false main.typ` to generate the PDF
// Packages
#import "@preview/catppuccin:1.0.0": catppuccin, flavors

// Colors controled by the `--input colored` variable passed in the command line or by default which is `false` and help to manage the default (preview in url) and uncolored (published in pdf) version.
//
// Get the `colored` variable from the command line input
// Then determine the color scheme based on the `colored` variable
#let inputs = sys.inputs
#let get_input(input_dict) = {
  let colored = true
  let preview = true
  for (key, value) in input_dict {
    if key == "colored" {
      colored = value
    }
    if key == "preview" {
      preview = value
    }
  }
  return (colored: colored, preview: preview)
}

#let (colored, preview) = get_input(inputs)

#let get_color_scheme(input_value) = {
  if input_value == "false" {
    // identity function for the default color scheme
    (
      background: doc => doc,
      flavors: flavors.latte,
    )
  } else {
    // use the mocha flavor for the colored scheme
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
#let text_color = {
  if colored == "false" {
    black
  } else {
    color_flavors.colors.text.rgb
  }
}
#let text_size = {
  if preview == true {
    11pt
  } else {
    9pt
  }
}
#let custume_text = (
  size: text_size,
  fill: text_color,
)

// Title and author information
#let conf(
  title: "Title",
  author: "Xinyu Xiang",
  date: datetime,
  year: none,
  textsize: none,
  doc,
) = {
  let textsize = { if textsize == none { custume_text.size } else { textsize } }
  set page(
    paper: "us-letter",
    header: context [
      #set text(size: textsize)
      #stack(
        spacing: textsize / 2,
        [#smallcaps[#year]
          #h(1fr)
          #smallcaps[#title]
          #h(1fr)
          #counter(page).display(
            "1/1",
            both: true,
          )],
        line(length: 100%, stroke: 0.6pt + custume_text.fill),
      )
    ],
  )
  set par(justify: true)
  set text(size: textsize, fill: custume_text.fill)
  align(center, text(18pt)[ *#title* ])
  align(center, text(12pt)[ #emph(author) ])
  align(center, text(12pt)[ #emph(date) ])
  doc
}

// block styles
#let definition(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.blue.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.mantle.rgb),
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
    fill: rgb(color_flavors.colors.mantle.rgb),
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
    fill: rgb(color_flavors.colors.mantle.rgb),
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
    fill: rgb(color_flavors.colors.mantle.rgb),
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
    fill: rgb(color_flavors.colors.mantle.rgb),
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
    fill: rgb(color_flavors.colors.mantle.rgb),
    inset: (x: 8pt, y: 8pt),
  )[
    #if name != none [_Proof_. (#emph(name)). ] else [_Proof_. ]
    #body
    #h(1fr)
    $qed$
  ]
}
