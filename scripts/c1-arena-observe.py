#!/usr/bin/env python3
"""Report the exact metadata seen by cloud CI without updating any pin."""
import hashlib
import json
from pathlib import Path
import urllib.request

root = Path(__file__).resolve().parents[1]
source = json.loads((root / 'tests/c1/arena-source.json').read_text())
request = urllib.request.Request(source['metadata_url'], headers={'User-Agent': 'PSKernel-C1-snapshot-review'})
with urllib.request.urlopen(request, timeout=60) as response:
    content = response.read(32 * 1024**2 + 1)
if len(content) > 32 * 1024**2:
    raise ValueError('metadata exceeds capture limit')
metadata = json.loads(content)
report = {'sha256': hashlib.sha256(content).hexdigest(), 'top_level_keys': list(metadata),
          'meta': metadata.get('meta'), 'metadata': metadata.get('metadata'),
          'expected_revision': source['arena_revision']}
print(json.dumps(report, indent=2), flush=True)
out = root / '_tmp/c1-next'
out.mkdir(parents=True, exist_ok=True)
(out / 'observed-metadata.json').write_bytes(content)
(out / 'observed-metadata-summary.json').write_text(json.dumps(report, indent=2) + '\n')
