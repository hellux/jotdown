## [0.8.1](https://github.com/hellux/jotdown/releases/tag/0.8.1) - 2025-08-18

### Fixed

- Incorrect parsing of link spans with unicode characters (#92).

## [0.8.0](https://github.com/hellux/jotdown/releases/tag/0.8.0) - 2024-04-23

### Fixed

- Span of merged dangling block attributes.
- Events missing for dangling attributes at the end of a block (#70).
- Multi-line comments broken in inline attributes (#74).
- Labeled links at start of line incorrectly parsed as link definitions (#81).
- Repeated attributes on link definitions being overwritten (#83).
- Div being closed by a div fence inside a raw block (#87).
- Spans breaking due to preceding exclamation mark (#88).

### Changed

- (breaking) Code block can now be closed by any longer fence (#84).
- (breaking) Remove the RenderRef trait.

## [0.7.0](https://github.com/hellux/jotdown/releases/tag/0.7.0) - 2024-12-08

### Changed

- (breaking) HTML renderer: use interactive `<input>` elements for task list items (#64).

## [0.6.0](https://github.com/hellux/jotdown/releases/tag/0.6.0) - 2024-09-22

### Added

- (breaking) `ListBulletType` to `ListKind::Unordered` and `ListKind::Task` in
  order to specify which bullet character was used for the list item (#57).
- (breaking) HTML renderer: configurable formatting, with minified or indented
  options (#58, #59).
- CLI: arguments for HTML formatting options.

## [0.5.0](https://github.com/hellux/jotdown/releases/tag/0.5.0) - 2024-08-24

### Added

- (breaking) `Attributes` events for dangling attribute sets (#56).
- Implement TryFrom<&str> for `Attributes`, allowing to use the attributes
  parser on its own (#56).
- More examples in documentation (#56).
- `AttributeValue::new`, `AttributeValue::default` (#56).

### Changed

- (breaking) Replace `Render::push_borrowed`, `Render::write_borrowed` with
  `RenderRef::push_ref`, `RenderRef::write_ref`.
- (breaking) Turn map-like opaque `Attributes` into wrapper of Vec<"AttributeElem"> (#56).
- (breaking) Preserve comments and duplicate values in attributes (#55, #56)
  (but still do not render).
- (breaking) Block attributes followed by a blank line are not attached to the next block.

### Fixed

- Remove extra whitespaces in attribute values (#56).

## [0.4.1](https://github.com/hellux/jotdown/releases/tag/0.4.1) - 2024-07-02

### Added

- Convenience function `html::render_to_string` (#49)

### Fixed

- Allow backslash at end of verbatim (#54)

## [0.4.0](https://github.com/hellux/jotdown/releases/tag/0.4.0) - 2024-03-20

### Added

- IntoIterator for Attributes (#33, #45)

### Changed

- Match djot.js how to resolve ordered list item type (#47).
- HTML renderer: use Unicode punctuation instead of HTML entities (#48).
- Allow omitting closing % in attribute comments (#48).

### Fixed

- Alphabetical list unexpectedly turning into roman numeral list (#46)
- HTML renderer: remove accidental extra variation selector in backarrow (#48).

## [0.3.2](https://github.com/hellux/jotdown/releases/tag/0.3.2) - 2023-09-06

### Changed

- Alphabetic list markers can only be one character long.

## [0.3.1](https://github.com/hellux/jotdown/releases/tag/0.3.1) - 2023-08-05

### Changed

- Block parser performance improved, up to 15% faster.
- Last `unsafe` block removed (#5).

### Fixed

- Do not require indent for continuing footnotes.
- Transfer classes from reference definitions to links.
- Allow line breaks in reference links (still match reference label).
- Remove excess newline after raw blocks.
- HTML renderer: fix missing `<p>` tags after ordered lists (#44).

## [0.3.0](https://github.com/hellux/jotdown/releases/tag/0.3.0) - 2023-05-16

### Added

- Source maps, via `Parser::into_offset_iter` (#39).

### Changed

- (breaking) `Render::render_event` has been removed (#36),
  `Render::{push,write}{,_borrowed}` take non-mutable reference of self.
- (breaking) Link definitions events are emitted (#36).
- (breaking) Footnote events are emitted as they are encountered (#36), instead
  of at the end of the document.
- Empty spans are parsed as spans when followed by URL, label or attributes.
- (breaking) Div class is non-optional, no class yields empty class string.
- (breaking) `Container::CodeBlock.lang` renamed to `language`.
- (breaking) Code block language is non-optional, no specfier yields empty
  string.
- Only ASCII whitespace is considered whitespace (#40).
- Performance improved, up to 20% faster (#40).

### Fixed

- Unclosed attributes after verbatim.
- Referenced headings with whitespace.
- Order of heading ids during lookup.
- Closing of math containers that end with backticks.
- Sole math containers in table cells.
- Attributes inside verbatim (#41).

## [0.2.1](https://github.com/hellux/jotdown/releases/tag/0.2.1) - 2023-04-25

### Changed

- Performance improved for inline parsing, up to 80% faster (#37).

### Fixed

- URL of autolink exit event (#35).

## [0.2.0](https://github.com/hellux/jotdown/releases/tag/0.2.0) - 2023-04-04

### Added

- Arguments to CLI (#8).
- Render trait (#12).
- Support for escapes in attributes (#19).
- Clone implementation for `Event` (#24).
- Rendering of borrowed `Event`s (#29).
- Clone implementation for `Parser` (#30).

### Changed

- (breaking) HTML rendering is done via the Render trait (#12).
- (breaking) Attribute values are represented by a custom `AttributeValue` type
  (#19).
- (breaking) Link `Event`s now expose unresolved reference labels (#27).
- Performance improved for inline parsing, up to 40% faster (#30).

### Fixed

- Incorrect parsing when multiple list items start on same line.
- List tightness.
- Disappearing attributes after inline verbatim (#16).
- Invalid HTML due to img tags (#25).
- Email autolink events not marked as Email (#27).
- Link text reference labels not stripping formatting (#22).
- Disappearing consecutive attribute sets (#34).

## [0.1.0](https://github.com/hellux/jotdown/releases/tag/0.1.0) - 2023-02-05

Initial Release.
