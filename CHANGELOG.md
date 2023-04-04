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
