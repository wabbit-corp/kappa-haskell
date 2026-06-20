# Kappa Image Loader

This package expands the original PNG parser into a small multi-format image loader.

Decision: the next target is **QOI, the Quite OK Image Format**.

Why QOI instead of BMP, GIF, TIFF, JPEG, or WebP:

- BMP is easy but mostly teaches header archaeology and padding trivia.
- GIF adds LZW and palette animation complexity, which is useful later but noisy now.
- JPEG/WebP would showcase codecs, not Kappa's binary-protocol story, unless half the project becomes math and entropy decoding.
- TIFF is a bag of tags wearing a trench coat. Useful eventually. Terrible second target.
- QOI is small, lossless, byte-oriented, stateful, and decodable in one pass. It forces a real loader abstraction and returns pixels without needing zlib.

So this version supports:

```text
PNG  -> validated PNG container, CRC, IHDR/PLTE/IDAT/IEND rules, compressed IDAT returned
QOI  -> validated header, chunk decoding, RGB/RGBA raster pixels returned
```

## Public API

```kappa
-- Format-neutral loader
sniff      : Bytes -> Option ImageFormat
loadImage  : Bytes -> Result ImageLoadError ImageDocument
loadRaster : Bytes -> Result ImageLoadError RasterImage

-- PNG container parser
parsePng             : Bytes -> Result PngError PngImage
parsePngUncheckedCrc : Bytes -> Result PngError PngImage
parsePngWith         : CrcPolicy -> Bytes -> Result PngError PngImage

-- QOI raster decoder
parseQoi : Bytes -> Result QoiError QoiImage
```

`loadImage` accepts either PNG or QOI by magic bytes. `loadRaster` currently succeeds for QOI and rejects PNG with `RasterDecodeUnavailable FormatPng`, because the PNG side intentionally stops at validated container parsing until a zlib + PNG scanline decoder is added. That is a boundary, not laziness. Well, not only laziness.

## Layout

```text
src/acme/image/core.kp       format-neutral image and loader errors
src/acme/image/loader.kp     magic sniffing and dispatch

src/acme/png/...             original PNG container parser

src/acme/qoi/core.kp         QOI model and errors
src/acme/qoi/binary.kp       byte cursor and big-endian readers
src/acme/qoi/parser.kp       QOI one-pass raster decoder
src/acme/qoi/example.kp      tiny embedded QOI fixtures

test/acme/png/...            PNG parser tests
test/acme/qoi/...            QOI parser tests
test/acme/image/...          format-neutral loader tests
```

## QOI decoder coverage

The decoder validates:

```text
magic bytes "qoif"
14-byte header shape
big-endian width / height
channels = 3 or 4
colorspace = 0 or 1
pixel-count safety limit
QOI_OP_RGB
QOI_OP_RGBA
QOI_OP_INDEX
QOI_OP_DIFF
QOI_OP_LUMA
QOI_OP_RUN
8-byte end marker
no trailing bytes
run overflow against image pixel count
```

It returns strict RGB or RGBA pixel bytes in row-major order.

## Backend note

The parsing and decoding logic is common Kappa source. The only selected-fragment native surface remains `acme.png.prim`, which supplies byte-to-number, byte wrapping addition, and unsigned-32 CRC helpers through JVM and .NET fragments. The package keeps host details out of the loader and format modules, because apparently shoving host APIs into every parser was not enough punishment for one species.

## Production gaps

```text
PNG raster decoding still needs zlib inflate + PNG filtering.
QOI encoder is not included.
Streaming decode surfaces are not included yet; this version decodes into strict Bytes.
The Kappa compiler/runtime is not available in this environment, so this source was not compile-run.
```
