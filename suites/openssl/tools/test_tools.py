"""Offline regression checks for image pins and the optional source downloader."""
import hashlib
import io
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import fetch_sources
import gen_image


class Pins(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.target = self.root / "targets/openssl_chacha20"
        # Deliberately omit the ignored vendor cache and all binary files.
        source = gen_image.ROOT
        rels = ["targets/openssl_chacha20/target.json", "Ssl/OpensslChacha20/Image.lean"]
        rels += [str(p.relative_to(source)) for p in (source / "targets/openssl_chacha20/image").iterdir()]
        for rel in rels:
            dest = self.root / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / rel, dest)
        self.enterContext(patch.object(gen_image, "ROOT", self.root))
        self.enterContext(patch.object(fetch_sources, "ROOT", self.root))

    def test_image_without_sources_or_binary(self):
        data, symbols = gen_image.pinned_image("openssl_chacha20")
        self.assertEqual(len(data), 1072)
        self.assertIn("ChaCha20_ctr32", symbols)

    def test_changed_bytes_and_decoder(self):
        path = self.root / "Ssl/OpensslChacha20/Image.lean"
        original = path.read_text()
        for old, new in [("def chunk0 : Nat := 0x", "def chunk0 : Nat := 0x1"),
                         ("(8 * (i % chunkSize))", "(7 * (i % chunkSize))")]:
            path.write_text(original.replace(old, new))
            with self.assertRaises((SystemExit, OverflowError)):
                gen_image.pinned_image("openssl_chacha20")

    def test_changed_symbols(self):
        path = self.target / "image/openssl_chacha20.syms.json"
        path.write_text(path.read_text() + " ")
        with self.assertRaises(SystemExit):
            gen_image.pinned_image("openssl_chacha20")

    def test_changed_disassembly_and_extra_file(self):
        path = self.target / "image/openssl_chacha20.dis"
        original = path.read_text()
        path.write_text(original.replace("retl", "ret "))
        with self.assertRaises(SystemExit):
            gen_image.pinned_image("openssl_chacha20")
        path.write_text(original)
        (self.target / "image/extra.bin").write_bytes(b"unpinned")
        with self.assertRaises(SystemExit):
            gen_image.pinned_image("openssl_chacha20")

    def test_download_verifies_before_writing_and_reuses_cache(self):
        data = b"pinned source\n"
        (self.target / "SOURCES.sha256").write_text(hashlib.sha256(data).hexdigest() + "  ./crypto/test.c\n")
        path = self.target / "vendor/crypto/test.c"
        with patch("urllib.request.urlopen", return_value=io.BytesIO(b"wrong source")):
            with self.assertRaises(SystemExit):
                fetch_sources.fetch("openssl_chacha20")
        self.assertFalse(path.exists())
        with patch("urllib.request.urlopen", return_value=io.BytesIO(data)) as request:
            fetch_sources.fetch("openssl_chacha20")
            request.assert_called_once_with(fetch_sources.BASE + "crypto/test.c", timeout=60)
        with patch("urllib.request.urlopen", side_effect=AssertionError("network used")):
            fetch_sources.fetch("openssl_chacha20")
            path.write_bytes(b"corrupted cache")
            with self.assertRaises(SystemExit):
                fetch_sources.fetch("openssl_chacha20")


if __name__ == "__main__":
    unittest.main()
