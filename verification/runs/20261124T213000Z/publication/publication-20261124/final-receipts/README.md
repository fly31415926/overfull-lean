# Actual publication observations

This lossless archive contains the genuine canonical tree, commit, fetch, verification, and branch-update observations through the cutoff in manifest.json. It includes the complete integrity report and actual connector responses. Repeated content-upload payloads remain represented by their recorded hashes and the public file bytes they created.

Run `python3 restore.py NEW_DIRECTORY` from a clone of this directory. The restorer checks every part, the compressed archive, the inventory, and every original file before writing the recovered bytes.

The recorded branch readbacks show both requested branches at `dc2f17c481b9bbffbbc81296a95ba0f203487cd0`. This archive is attached by a publication-only child of that commit. Final live branch positions are checked after the attachment is published.
