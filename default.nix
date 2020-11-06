{ mkDerivation, base, containers, haskeline, hedgehog, hpack, hspec
, megaparsec, microlens, microlens-th, mtl, parsers, prettyprinter
, raw-strings-qq, recursion-schemes, repline, selective, stdenv
, text, transformers
}:
mkDerivation {
  pname = "HowardLang";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base containers haskeline megaparsec microlens microlens-th mtl
    parsers prettyprinter recursion-schemes repline selective text
    transformers
  ];
  libraryToolDepends = [ hpack ];
  executableHaskellDepends = [
    base containers haskeline megaparsec microlens microlens-th mtl
    parsers prettyprinter recursion-schemes repline selective text
    transformers
  ];
  testHaskellDepends = [
    base containers haskeline hedgehog hspec megaparsec microlens
    microlens-th mtl parsers prettyprinter raw-strings-qq
    recursion-schemes repline selective text transformers
  ];
  prePatch = "hpack";
  homepage = "https://github.com/ssbothwell/HowardLang#readme";
  license = stdenv.lib.licenses.bsd3;
}
