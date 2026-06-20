# Design note: why QOI is the second format

The original PNG parser proves container validation: signature, chunk layout, CRC-32, and PNG ordering rules. It deliberately does not inflate IDAT or unfilter scanlines.

The next format needed to prove a different part of the language story:

1. byte-level cursor parsing;
2. stateful decoding;
3. bounded table updates;
4. wraparound byte arithmetic;
5. common loader dispatch;
6. strict raster bytes as an output;
7. no giant external codec dependency.

QOI hits all seven. It has a fixed 14-byte header, a tiny opcode set, a 64-entry pixel index, and a simple end marker. That makes it ideal as the first fully decoded format after PNG.

The common loader deliberately returns either:

```kappa
DecodedRaster FormatQoi raster
PngContainer png
```

rather than pretending all formats already produce decoded pixels. When the PNG decoder grows zlib + filtering, it can start returning `DecodedRaster FormatPng raster` through the same facade.
