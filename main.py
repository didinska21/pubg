"""
PAK File Manager - Enhanced with Manifest Support

IMPORTANT NOTES ON REPACKING:
==============================

1. FILE SIZE MATTERS:
   - You can only repack files that fit within their original allocated space (slots)
   - If your modified file is larger than the original, it may not fit even with maximum compression
   - The tool will try all compression levels (1-22) to find the best fit

2. FILE MATCHING:
   - Files are matched by name AND path structure
   - If you have multiple files with the same name (e.g., Item.uasset), organize them in subfolders
   - Example structure:
     unpacked/
       └── my_pak_name/
           └── edited/
               ├── Content/IN/CSV/Item.uasset
               └── InGame/EvoBase/CSV/Item.uasset
   
3. WHY REPACKING FAILS:
   - The modified file is larger than the original uncompressed size
   - Even with maximum compression, the compressed data doesn't fit in the allocated slot
   - Wrong file matched (multiple files with same name)
   
4. COMPRESSION METHODS:
   - The tool uses ZSTD dictionary compression (ZSTD_DICT) when available
   - It tries all levels from 22 (best) down to 1 (fastest)
   - Encryption (SM4) is applied after compression

5. WHAT TO DO IF REPACK FAILS:
   - Check if your modified file is significantly larger than the original
   - Verify you're editing the correct file (check the path match)
   - Consider reducing your modifications to keep file size similar to original
   - Use the manifest viewer (option 4) to check expected file sizes

"""

import os
import itertools as it
# Compatibility fix for Python versions older than 3.12
if not hasattr(it, 'batched'):
    def batched(iterable, n):
        import itertools
        if n < 1:
            raise ValueError('n must be at least one')
        it_obj = iter(iterable)
        while batch := tuple(itertools.islice(it_obj, n)):
            yield batch
    it.batched = batched
import math
import struct
import zlib
from dataclasses import dataclass
from functools import lru_cache
from pathlib import PurePath, Path
import gmalg
from Crypto.Cipher import AES
from Crypto.Cipher.AES import MODE_CBC
from Crypto.Hash import SHA1
from Crypto.Util.Padding import unpad, pad
from zstandard import ZstdDecompressor, ZstdCompressor, ZstdCompressionDict, DICT_TYPE_AUTO
import const
import sys
import subprocess
import platform
import hashlib
import base64
import requests
# Initialize colorama for Windows color support
try:
    import colorama
    colorama.init(autoreset=True)
except ImportError:
    pass  # colorama not installed, colors may not work on Windows

from rich.console import Console
from rich.panel import Panel
from rich.table import Table
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn, TimeElapsedColumn
console = Console()
from sm4_variant import SM4
import json
from datetime import datetime
import shutil
import traceback

# ==================== MISC CLASSES ====================
class Misc:
    @staticmethod
    def pad_to_n(data: bytes, n: int) -> bytes:
        assert n > 0
        padding = n - len(data) % n
        if padding == n:
            return data
        else:
            return data + b'\x00' * padding
    @staticmethod
    def align_up(x: int, n: int) -> int:
        return (x + n - 1) // n * n

class Reader:
    def __init__(self, buffer, cursor=0):
        self._buffer = buffer
        self._cursor = cursor
    def u1(self, move_cursor=True) -> int:
        return self.unpack('B', move_cursor=move_cursor)[0]
    def u4(self, move_cursor=True) -> int:
        return self.unpack('<I', move_cursor=move_cursor)[0]
    def u8(self, move_cursor=True) -> int:
        return self.unpack('<Q', move_cursor=move_cursor)[0]
    def i1(self, move_cursor=True) -> int:
        return self.unpack('b', move_cursor=move_cursor)[0]
    def i4(self, move_cursor=True) -> int:
        return self.unpack('<i', move_cursor=move_cursor)[0]
    def i8(self, move_cursor=True) -> int:
        return self.unpack('<q', move_cursor=move_cursor)[0]
    def s(self, n: int, move_cursor=True) -> bytes:
        return self.unpack(f'{n}s', move_cursor=move_cursor)[0]
    def unpack(self, f: str | bytes, offset=0, move_cursor=True):
        x = struct.unpack_from(f, self._buffer, self._cursor + offset)
        if move_cursor:
            self._cursor += struct.calcsize(f)
        return x
    def string(self, move_cursor=True) -> str:
        length = self.i4(move_cursor=move_cursor)
        if length == 0:
            return str()
        else:
            assert length > 0
            offset = 0 if move_cursor else 4
            return self.unpack(f'{length}s', offset=offset, move_cursor=move_cursor)[0].rstrip(b'\x00').decode()

class Writer:
    def __init__(self):
        self._buffer = bytearray()
    def u1(self, value: int) -> None:
        self.pack('B', value)
    def u4(self, value: int) -> None:
        self.pack('<I', value)
    def u8(self, value: int) -> None:
        self.pack('<Q', value)
    def i1(self, value: int) -> None:
        self.pack('b', value)
    def i4(self, value: int) -> None:
        self.pack('<i', value)
    def i8(self, value: int) -> None:
        self.pack('<q', value)
    def s(self, data: bytes) -> None:
        self._buffer.extend(data)
    def pack(self, f: str, *values) -> None:
        self._buffer.extend(struct.pack(f, *values))
    def string(self, text: str) -> None:
        encoded = text.encode() + b'\x00'
        self.i4(len(encoded))
        self.s(encoded)
    def get_buffer(self) -> bytes:
        return bytes(self._buffer)
    def size(self) -> int:
        return len(self._buffer)
    def align_to(self, alignment: int) -> None:
        current_size = len(self._buffer)
        padding = (alignment - current_size % alignment) % alignment
        if padding > 0:
            self._buffer.extend(b'\x00' * padding)

# ==================== BLOCK LOGGER ====================
class BlockLogger:
    """Detailed logging for each compression block"""
    def __init__(self, filename: str):
        self.filename = filename
        self.blocks = []
        self.original_total_size = 0
        self.compressed_total_size = 0
        
    def add_block(self, block_index: int, original_size: int, compressed_size: int, 
                  compression_method: str, level: int, success: bool, 
                  block_offset: int, block_end: int):
        block_data = {
            'index': block_index,
            'original_size': original_size,
            'compressed_size': compressed_size,
            'compression_ratio': compressed_size / original_size if original_size > 0 else 0,
            'savings_percent': (1 - (compressed_size / original_size)) * 100 if original_size > 0 else 0,
            'compression_method': compression_method,
            'level': level,
            'success': success,
            'block_offset': block_offset,
            'block_end': block_end,
            'slot_size': block_end - block_offset,
            'utilization': (compressed_size / (block_end - block_offset)) * 100 if (block_end - block_offset) > 0 else 0
        }
        self.blocks.append(block_data)
        self.original_total_size += original_size
        self.compressed_total_size += compressed_size
        
    def print_summary(self):
        table = Table(title=f"📊 Block Compression Summary: {self.filename}", show_header=True, header_style="bold magenta")
        table.add_column("Block", style="cyan", width=6)
        table.add_column("Original", justify="right", width=12)
        table.add_column("Compressed", justify="right", width=12)
        table.add_column("Slot Size", justify="right", width=12)
        table.add_column("Free", justify="right", width=10)
        table.add_column("Method", width=12)
        table.add_column("Lvl", justify="center", width=5)
        table.add_column("Status", width=8)
        
        for block in self.blocks:
            status = "✅" if block['success'] else "❌"
            slot_size = block['slot_size']
            compressed = block['compressed_size']
            
            # FIXED: Free space should be: slot - compressed
            # Positive = space left, Negative = overflow
            free_space = slot_size - compressed
            
            # Handle REUSED in method name
            method = block['compression_method']
            level = str(block['level'] if block['level'] != -1 else "N/A")
            
            # Color code free space
            # Positive (green) = fits with room to spare
            # Near zero (yellow) = tight fit
            # Negative (red) = overflow, doesn't fit
            if free_space >= 0:
                free_str = f"[green]+{free_space:,}[/green]"
                if free_space < 100:
                    free_str = f"[yellow]+{free_space:,}[/yellow]"
            else:
                free_str = f"[red]{free_space:,}[/red]"  # Already has minus sign
            
            table.add_row(
                str(block['index']),
                f"{block['original_size']:,}",
                f"{compressed:,}",
                f"{slot_size:,}",
                free_str,
                method,
                level,
                status
            )
        
        console.print(table)
        
        # Overall summary
        overall_ratio = self.compressed_total_size / self.original_total_size if self.original_total_size > 0 else 0
        overall_savings = (1 - overall_ratio) * 100
        total_slot_size = sum(b['slot_size'] for b in self.blocks)
        total_free = total_slot_size - self.compressed_total_size
        
        console.print(f"\n📈 Overall Summary:")
        console.print(f"   Original Size: {self.original_total_size:,} bytes")
        console.print(f"   Compressed Size: {self.compressed_total_size:,} bytes")
        console.print(f"   Total Slot Size: {total_slot_size:,} bytes")
        console.print(f"   Free Space: {total_free:,} bytes ({(total_free/total_slot_size)*100:.1f}% unused)")
        console.print(f"   Compression Ratio: {overall_ratio:.3f} ({overall_savings:.1f}% savings)")
        console.print(f"   Total Blocks: {len(self.blocks)}")


# ==================== REPACK LOGGER ====================
class RepackLogger:
    """Logging for repack operations"""
    def __init__(self):
        self.successes = []
        self.failures = []
        
    def log_success(self, file_name: str, compressed_size: int, slot_size: int):
        self.successes.append({
            'file': file_name,
            'compressed': compressed_size,
            'slot': slot_size,
            'ratio': (compressed_size / slot_size) * 100 if slot_size > 0 else 0
        })
        
    def log_failure(self, file_name: str, reason: str, details: dict):
        self.failures.append({
            'file': file_name,
            'reason': reason,
            'details': details
        })
        
    def print_summary(self):
        if not self.successes and not self.failures:
            console.print("⚠️ No repack operations logged")
            return
        
        # Success table
        if self.successes:
            success_table = Table(title="✅ Successful Repacks", show_header=True, header_style="bold green")
            success_table.add_column("File", style="cyan")
            success_table.add_column("Compressed", justify="right")
            success_table.add_column("Slot", justify="right")
            success_table.add_column("Utilization", justify="right")
            
            for s in self.successes:
                success_table.add_row(
                    s['file'],
                    f"{s['compressed']:,}",
                    f"{s['slot']:,}",
                    f"{s['ratio']:.1f}%"
                )
            
            console.print(success_table)
        
        # Failure table
        if self.failures:
            failure_table = Table(title="❌ Failed Repacks", show_header=True, header_style="bold red")
            failure_table.add_column("File", style="cyan")
            failure_table.add_column("Reason", style="white")
            failure_table.add_column("Details", style="dim")
            
            for f in self.failures:
                details_str = ", ".join(f"{k}: {v}" for k, v in f['details'].items())
                failure_table.add_row(
                    f['file'],
                    f['reason'],
                    details_str if details_str else "-"
                )
            
            console.print(failure_table)
        
        # Overall panel
        total = len(self.successes) + len(self.failures)
        success_rate = (len(self.successes) / total * 100) if total > 0 else 0
        console.print(Panel(
            f"[green]Successes: {len(self.successes)}[/green]\n"
            f"[red]Failures: {len(self.failures)}[/red]\n"
            f"Success Rate: {success_rate:.1f}%",
            title="[bold]Repack Summary[/bold]"
        ))
        
# ==================== MANIFEST CLASSES ====================
class ManifestGenerator:
    """Generate manifest.json in real-time during unpack"""
    def __init__(self, pak_name: str, output_path=None):
        self.pak_name = pak_name
        self.output_path = output_path  # Real-time write location
        self.manifest = {
            'pak_file': pak_name,
            'created_at': datetime.now().isoformat(),
            'version': '3.0',  # UPDATED: Version bump for enhanced block tracking
            'total_files': 0,
            'total_blocks': 0,
            'compression_stats': {},
            'encryption_stats': {},
            'extraction_mode': 'full',
            'files': {},
            'block_files': {},  # Dictionary of block files keyed by extracted filename
            'block_file_mappings': {}  # NEW: Mapping from block filename to original file
        }
        
    def set_extraction_mode(self, use_block_splitting: bool):
        """Set whether blocks are being extracted separately"""
        self.manifest['extraction_mode'] = 'blocks' if use_block_splitting else 'full'
    
    def add_block_file_entry(self, original_file_path, block_index: int, block_size: int, entry):
        """Track individual block file entry (for block-based extraction)"""
        file_key = str(original_file_path).replace('\\', '/')
        
        # Create extracted filename (how it's actually saved on disk)
        filename = Path(original_file_path).name
        stem = Path(filename).stem
        ext = Path(filename).suffix
        extracted_filename = f"{stem}_block_{block_index}{ext}"
        
        # Map compression methods
        comp_names = {
            0: 'CM_NONE',
            1: 'CM_ZLIB',
            6: 'CM_ZSTD',
            8: 'CM_ZSTD_DICT'
        }
        
        compression_name = comp_names.get(entry.compression_method, f'UNKNOWN_{entry.compression_method}')
        
        # Store block file metadata with extracted filename as key
        block_entry = {
            'parent_file': file_key,
            'block_index': block_index,
            'block_size': block_size,
            'extracted_filename': extracted_filename,
            'original_filename': filename,
            'compression_method': entry.compression_method,
            'compression_method_name': compression_name,
            'encrypted': entry.encrypted,
            'encryption_method': entry.encryption_method if entry.encrypted else 0,
        }
        
        # Store in block_files dictionary with extracted filename as key
        self.manifest['block_files'][extracted_filename] = block_entry
        
        # Also store in mapping for quick lookup
        self.manifest['block_file_mappings'][extracted_filename] = file_key
        
        # Also keep track of parent file metadata
        if file_key not in self.manifest['files']:
            self.manifest['files'][file_key] = {
                'uncompressed_size': entry.uncompressed_size,
                'compression_method': entry.compression_method,
                'compression_method_name': compression_name,
                'num_blocks': 0,
                'extracted_as_blocks': True,
                'block_filenames': []  # List of block filenames
            }
            self.manifest['total_files'] += 1
        
        # Add block filename to parent's list
        self.manifest['files'][file_key]['block_filenames'].append(extracted_filename)
        
        # Increment block count
        self.manifest['files'][file_key]['num_blocks'] += 1
        
        if self.output_path:
            self._write_realtime()
        
    def add_file_entry(self, file_path, entry, actual_offset: int, actual_size: int):
        if entry.encrypted and entry.encryption_method == 17:
            return
            
        file_key = str(file_path).replace('\\', '/')
        
        # Map compression methods - From const.py
        comp_names = {
            0: 'CM_NONE',
            1: 'CM_ZLIB',
            6: 'CM_ZSTD',
            8: 'CM_ZSTD_DICT'
        }
        
        # Map encryption methods - From const.py (with SM4_NEW inference)
        enc_names = {
            1: 'EM_SIMPLE1',
            2: 'EM_SM4_2',
            4: 'EM_SM4_4',
            16: 'EM_SIMPLE2',
            17: 'EM_UNKNOWN_17',
            31: 'EM_SM4_NEW_31',
            32: 'EM_SM4_NEW_32',
            33: 'EM_SM4_NEW_33',
            34: 'EM_SM4_NEW_34',
            35: 'EM_SM4_NEW_35',
            36: 'EM_SM4_NEW_36',
            37: 'EM_SM4_NEW_37',
            38: 'EM_SM4_NEW_38',
            39: 'EM_SM4_NEW_39',
            40: 'EM_SM4_NEW_40',
            41: 'EM_SM4_NEW_41',
            42: 'EM_SM4_NEW_42',
            43: 'EM_SM4_NEW_43',
            44: 'EM_SM4_NEW_44',
            45: 'EM_SM4_NEW_45',
            0: 'NONE',
        }
        
        # Get encryption name
        if entry.encrypted:
            encryption_name = enc_names.get(entry.encryption_method, f'UNKNOWN_{entry.encryption_method}')
        else:
            encryption_name = 'NONE'
            
        # Get compression name
        compression_name = comp_names.get(entry.compression_method, f'UNKNOWN_{entry.compression_method}')
        
        # Build detailed block info
        block_info = []
        if hasattr(entry, 'compressed_blocks') and entry.compressed_blocks:
            for i, block in enumerate(entry.compressed_blocks):
                block_size = block.end - block.start
                block_info.append({
                    'index': i,
                    'start': block.start,
                    'end': block.end,
                    'size': block_size,
                    'offset_in_file': i * entry.compression_block_size if entry.compression_block_size > 0 else 0,
                    'max_size': entry.compression_block_size if entry.compression_block_size > 0 else block_size
                })
        
        file_entry = {
            'offset': actual_offset,
            'total_size': actual_size,
            'uncompressed_size': entry.uncompressed_size,
            'compression_method': entry.compression_method,
            'compression_method_name': compression_name,
            'compression_block_size': entry.compression_block_size,
            'encrypted': entry.encrypted,
            'encryption_method': entry.encryption_method if entry.encrypted else 0,
            'encryption_method_name': encryption_name,
            'blocks': block_info,
            'num_blocks': len(entry.compressed_blocks) if hasattr(entry, 'compressed_blocks') else 0,
            'content_hash': entry.content_hash.hex() if hasattr(entry, 'content_hash') and entry.content_hash else None,
            'unk1': entry.unk1 if hasattr(entry, 'unk1') else 0,
            'unk2': entry.unk2.hex() if hasattr(entry, 'unk2') and entry.unk2 else None
        }
        
        self.manifest['files'][file_key] = file_entry
        self.manifest['total_files'] += 1
        self.manifest['total_blocks'] += len(block_info)
        
        # Update compression stats
        comp_key = compression_name
        if comp_key not in self.manifest['compression_stats']:
            self.manifest['compression_stats'][comp_key] = 0
        self.manifest['compression_stats'][comp_key] += 1
        
        # Update encryption stats
        enc_key = encryption_name
        if enc_key not in self.manifest['encryption_stats']:
            self.manifest['encryption_stats'][enc_key] = 0
        self.manifest['encryption_stats'][enc_key] += 1
        
        # REAL-TIME: Write manifest immediately after each file
        if self.output_path:
            self._write_realtime()
    
    def _write_realtime(self):
        """Write manifest to disk in real-time (after each file)"""
        try:
            output_path = Path(self.output_path)
            if not output_path.exists():
                output_path.mkdir(parents=True, exist_ok=True)
            
            manifest_file = output_path / 'manifest.json'
            
            # Add summary stats
            self.manifest['summary'] = {
                'compression_distribution': self.manifest['compression_stats'],
                'encryption_distribution': self.manifest['encryption_stats'],
                'avg_blocks_per_file': self.manifest['total_blocks'] / self.manifest['total_files'] if self.manifest['total_files'] > 0 else 0
            }
            
            # Write to disk
            with open(manifest_file, 'w', encoding='utf-8') as f:
                json.dump(self.manifest, f, indent=2, ensure_ascii=False)
            
            # Show progress every 10 files
            if self.manifest['total_files'] % 10 == 0:
                print(f"[cyan]📋 Manifest updated: {self.manifest['total_files']} files")
        
        except Exception as e:
            print(f"[yellow]⚠️ Real-time manifest write error: {e}")
        
    def save(self, output_path):
        """Final save (manifest already written, just show summary)"""
        try:
            output_path = Path(output_path)
            
            if not output_path.exists():
                output_path.mkdir(parents=True, exist_ok=True)
            
            manifest_file = output_path / 'manifest.json'
            
            # Add summary stats
            self.manifest['summary'] = {
                'compression_distribution': self.manifest['compression_stats'],
                'encryption_distribution': self.manifest['encryption_stats'],
                'avg_blocks_per_file': self.manifest['total_blocks'] / self.manifest['total_files'] if self.manifest['total_files'] > 0 else 0
            }
            
            # Final write
            with open(manifest_file, 'w', encoding='utf-8') as f:
                json.dump(self.manifest, f, indent=2, ensure_ascii=False)
            
            # Print final summary
            console.print(Panel(
                f"[green]✅ Manifest Complete[/green]\n"
                f"• Location: {manifest_file}\n"
                f"• Files: {self.manifest['total_files']}\n"
                f"• Blocks: {self.manifest['total_blocks']}\n"
                f"• Compression: {', '.join(f'{k}:{v}' for k, v in self.manifest['compression_stats'].items())}\n"
                f"• Encryption: {', '.join(f'{k}:{v}' for k, v in self.manifest['encryption_stats'].items())}",
                title="[bold]Manifest Summary[/bold]"
            ))
            
            print(f"[green]✅ Manifest file verified at: {manifest_file}")
            return manifest_file
            
        except Exception as e:
            print(f"[red]❌ CRITICAL ERROR saving manifest:")
            print(f"[red]   {type(e).__name__}: {e}")
            traceback.print_exc()
            return None

class ManifestReader:
    """Read and use manifest data during repack"""
    def __init__(self, manifest_path):
        self.manifest_path = Path(manifest_path)
        self.manifest = {}
        self.extraction_mode = 'full'
        self.block_files = {}  # Dictionary of block files
        self.block_file_mappings = {}  # NEW: Mapping from block filename to original file
        self.load()
        
    def load(self):
        if not self.manifest_path.exists():
            raise FileNotFoundError(f'Manifest not found: {self.manifest_path}')
        
        with open(self.manifest_path, 'r', encoding='utf-8') as f:
            self.manifest = json.load(f)
        
        # Handle version 2.1 manifest (backward compatibility)
        manifest_version = self.manifest.get('version', '1.0')
        
        if manifest_version == '2.1':
            # Convert v2.1 format to v3.0 format
            self._convert_v21_to_v30()
        
        # Load extraction mode and block files
        self.extraction_mode = self.manifest.get('extraction_mode', 'full')
        self.block_files = self.manifest.get('block_files', {})
        self.block_file_mappings = self.manifest.get('block_file_mappings', {})
        
        # Show extraction mode info
        mode_display = "BLOCKS" if self.extraction_mode == 'blocks' else "FULL FILES"
        mode_color = "yellow" if self.extraction_mode == 'blocks' else "cyan"
        
        console.print(Panel(
            f"[green]📖 Manifest Loaded[/green]\n"
            f"• PAK: {self.manifest.get('pak_file', 'Unknown')}\n"
            f"• Files: {len(self.manifest.get('files', {}))}\n"
            f"• Version: {self.manifest.get('version', '1.0')}\n"
            f"• Extraction Mode: [{mode_color}]{mode_display}[/{mode_color}]",
            title="[bold]Repack Preparation[/bold]"
        ))
        
        # Show block mode warning
        if self.is_block_mode():
            block_count = len(self.block_files)
            console.print(f"[yellow]📦 Block mode detected - will reassemble {block_count} block files")
    
    def _convert_v21_to_v30(self):
        """Convert version 2.1 manifest format to version 3.0 format"""
        console.print("[yellow]⚠️ Converting manifest from v2.1 to v3.0 format...[/yellow]")
        
        # Create block_files dictionary if it doesn't exist
        if 'block_files' not in self.manifest:
            self.manifest['block_files'] = {}
        
        # Create block_file_mappings if it doesn't exist
        if 'block_file_mappings' not in self.manifest:
            self.manifest['block_file_mappings'] = {}
        
        # Process all files in the manifest
        for file_path, file_info in self.manifest.get('files', {}).items():
            if file_info.get('extracted_as_blocks'):
                block_filenames = file_info.get('block_files', [])
                
                for i, block_filename in enumerate(block_filenames):
                    # Create block entry
                    block_entry = {
                        'parent_file': file_path,
                        'block_index': i,
                        'block_size': 0,  # Size not stored in v2.1
                        'extracted_filename': block_filename,
                        'original_filename': Path(file_path).name,
                        'compression_method': file_info.get('compression_method', 0),
                        'compression_method_name': file_info.get('compression_method_name', 'UNKNOWN'),
                        'encrypted': file_info.get('encrypted', False),
                        'encryption_method': file_info.get('encryption_method', 0),
                    }
                    
                    # Add to block_files dictionary
                    self.manifest['block_files'][block_filename] = block_entry
                    
                    # Add to mappings
                    self.manifest['block_file_mappings'][block_filename] = file_path
        
        # Update version
        self.manifest['version'] = '3.0'
        console.print("[green]✅ Manifest converted to v3.0 format[/green]")
    
    def is_block_mode(self) -> bool:
        """Check if this manifest was created with block splitting"""
        return self.extraction_mode == 'blocks'
    
    def get_block_info_by_filename(self, block_filename: str):
        """Get block info for a specific block filename"""
        return self.block_files.get(block_filename)
    
    def get_original_file_for_block(self, block_filename: str):
        """Get original file path for a block filename"""
        return self.block_file_mappings.get(block_filename)
    
    def get_all_blocks_for_file(self, file_path: str):
        """Get all block entries for a given file"""
        normalized = file_path.replace('\\', '/')
        blocks = []
        
        for block_filename, block_info in self.block_files.items():
            if block_info.get('parent_file') == normalized:
                blocks.append(block_info)
        
        # Sort by block index
        blocks.sort(key=lambda x: x.get('block_index', 0))
        return blocks
        
    def find_file_info(self, file_path: str, quiet_on_exact_match=False):
        """Find file info by path (relative to mount point)
        
        Args:
            file_path: Path to search for
            quiet_on_exact_match: If True, don't print warnings when we have an exact match
        """
        # Try exact match first
        if file_path in self.manifest['files']:
            return self.manifest['files'][file_path]
        
        # Normalize path separators for comparison
        file_path_normalized = file_path.replace('\\', '/')
        for path in self.manifest['files']:
            if path.replace('\\', '/') == file_path_normalized:
                return self.manifest['files'][path]
        
        # Try filename only (least reliable, will return first match)
        filename = Path(file_path).name
        matches = []
        for path, info in self.manifest['files'].items():
            if Path(path).name == filename:
                matches.append((path, info))
        
        if len(matches) > 1 and not quiet_on_exact_match:
            console.print(f"[yellow]⚠️ Multiple manifest entries found for filename '{filename}':")
            for path, _ in matches:
                console.print(f"   • {path}")
            console.print(f"[yellow]   Using first match. Consider using full path for accuracy.")
        
        if matches:
            return matches[0][1]
        
        return None
    
    def get_file_blocks(self, file_path: str):
        """Get block information for a file"""
        info = self.find_file_info(file_path)
        if info and 'blocks' in info:
            return info['blocks']
        return []
    
    def print_file_details(self, file_path: str, quiet_on_exact_match=False):
        """Print detailed file information
        
        Args:
            file_path: Path to search for (can be full path or filename)
            quiet_on_exact_match: If True, don't print multiple match warnings when we have exact match
        """
        info = self.find_file_info(file_path, quiet_on_exact_match=quiet_on_exact_match)
        if not info:
            console.print(f"[yellow]⚠️ No manifest info for: {file_path}")
            return
        
        # Check if this was extracted as blocks
        if info.get('extracted_as_blocks'):
            blocks = self.get_all_blocks_for_file(file_path)
            console.print(f"[yellow]   📦 Extracted as {len(blocks)} block files")
            
            # Show expected block sizes
            if blocks:
                table = Table(show_header=True, header_style="bold cyan", box=None, pad_edge=False)
                table.add_column("Block", width=6)
                table.add_column("Filename", width=30)
                table.add_column("Size", justify="right", width=12)
                
                for block in blocks:
                    table.add_row(
                        str(block['block_index']),
                        block.get('extracted_filename', 'unknown'),
                        f"{block.get('block_size', 0):,}"
                    )
                
                console.print(table)
            return
        
        # Normal file display
        table = Table(title=f"📋 Manifest Details: {Path(file_path).name}", show_header=True)
        table.add_column("Property", style="cyan")
        table.add_column("Value", style="white")
        
        table.add_row("Compression", f"{info.get('compression_method_name', 'Unknown')} ({info.get('compression_method', 0)})")
        table.add_row("Encryption", f"{info.get('encryption_method_name', 'Unknown')} ({info.get('encryption_method', 0)})")
        table.add_row("Uncompressed Size", f"{info.get('uncompressed_size', 0):,} bytes")
        table.add_row("Total Size", f"{info.get('total_size', 0):,} bytes")
        table.add_row("Block Size", f"{info.get('compression_block_size', 0):,} bytes")
        table.add_row("Number of Blocks", str(info.get('num_blocks', 0)))
        
        if info.get('blocks'):
            table.add_row("Block Layout", f"{len(info['blocks'])} blocks, {sum(b['size'] for b in info['blocks']):,} total slot")
        
        console.print(table)
        
        # Print block details if available
        if info.get('blocks'):
            block_table = Table(title="Block Details", show_header=True)
            block_table.add_column("#", style="cyan", width=4)
            block_table.add_column("Start", justify="right", width=12)
            block_table.add_column("End", justify="right", width=12)
            block_table.add_column("Size", justify="right", width=12)
            block_table.add_column("Max", justify="right", width=12)
            
            for block in info['blocks']:
                block_table.add_row(
                    str(block['index']),
                    f"{block['start']:,}",
                    f"{block['end']:,}",
                    f"{block['size']:,}",
                    f"{block['max_size']:,}"
                )
            
            console.print(block_table)

# ==================== PAK STRUCTURE CLASSES ====================
class PakInfo:
    def __init__(self, buffer, keystream: list[int]):
        def decrypt_index_encrypted(x: int) -> int:
            MASK_8 = 255
            return (x ^ keystream[3]) & MASK_8
        def decrypt_magic(x: int) -> int:
            return x ^ keystream[2]
        def decrypt_index_hash(x: bytes) -> bytes:
            key = struct.pack('<5I', *keystream[4:][:5])
            assert len(x) == len(key)
            return bytes((a ^ b for a, b in zip(x, key)))
        def decrypt_index_size(x: int) -> int:
            return x ^ (keystream[10] << 32 | keystream[11])
        def decrypt_index_offset(x: int) -> int:
            return x ^ (keystream[0] << 32 | keystream[1])
        reader = Reader(buffer[-PakInfo._mem_size((-1)):])
        self.index_encrypted = decrypt_index_encrypted(reader.u1()) == 1
        self.magic = decrypt_magic(reader.u4())
        self.version = reader.u4()
        self.index_hash = decrypt_index_hash(reader.s(20)) if self.version >= 6 else bytes()
        self.index_size = decrypt_index_size(reader.u8())
        self.index_offset = decrypt_index_offset(reader.u8())
        if self.version <= 3:
            self.index_encrypted = False
    @staticmethod
    def _mem_size(_: int) -> int:
        return 45

class TencentPakInfo(PakInfo):
    def __init__(self, buffer, keystream: list[int]):
        def decrypt_unk(x: bytes) -> bytes:
            key = struct.pack('<8I', *keystream[7:][:8])
            assert len(x) == len(key)
            return bytes((a ^ b for a, b in zip(x, key)))
        def decrypt_stem_hash(x: int) -> int:
            return x ^ keystream[8]
        def decrypt_unk_hash(x: int) -> int:
            return x ^ keystream[9]
        super().__init__(buffer, keystream)
        reader = Reader(buffer[-TencentPakInfo._mem_size(self.version):])
        self.unk1 = decrypt_unk(reader.s(32)) if self.version >= 7 else bytes()
        self.packed_key = reader.s(256) if self.version >= 8 else bytes()
        self.packed_iv = reader.s(256) if self.version >= 8 else bytes()
        self.packed_index_hash = reader.s(256) if self.version >= 8 else bytes()
        self.stem_hash = decrypt_stem_hash(reader.u4()) if self.version >= 9 else 0
        self.unk2 = decrypt_unk_hash(reader.u4()) if self.version >= 9 else 0
        self.content_org_hash = reader.s(20) if self.version >= 12 else bytes()
    @staticmethod
    def _mem_size(version: int) -> int:
        size_for_7 = 32 if version >= 7 else 0
        size_for_8 = 768 if version >= 8 else 0
        size_for_9 = 8 if version >= 9 else 0
        size_for_12 = 20 if version >= 12 else 0
        return PakInfo._mem_size(version) + size_for_7 + size_for_8 + size_for_9 + size_for_12

class PakCompressedBlock:
    def __init__(self, reader: Reader):
        self.start = reader.u8()
        self.end = reader.u8()

@dataclass
class TencentPakEntry:
    def __init__(self, reader: Reader, version: int):
        self.content_hash = reader.s(20)
        if version <= 1:
            _ = reader.u8()
        self.offset = reader.u8()
        self.uncompressed_size = reader.u8()
        self.compression_method = reader.u4() & const.CM_MASK
        self.size = reader.u8()
        self.unk1 = reader.u1() if version >= 5 else 0
        self.unk2 = reader.s(20) if version >= 5 else bytes()
        self.compressed_blocks = [PakCompressedBlock(reader) for _ in range(reader.u4())] if self.compression_method != 0 and version >= 3 else []
        self.compression_block_size = reader.u4() if version >= 4 else 0
        self.encrypted = reader.u1() == 1 if version >= 4 else False
        self.encryption_method = reader.u4() if version >= 12 else 0
        self.index_new_sep = reader.u4() if version >= 12 else 0

# ==================== CRYPTO CLASS ====================

# ==================== COMPRESSION MANAGER ====================
class CompressionManager:
    """Handles compression with detailed logging and optimization"""
    
    @staticmethod
    def compress_block(data: bytes, compression_method: str, level: int, zstd_dict=None) -> bytes:
        """Compress a block with specific method and level"""
        if compression_method == 'NONE':
            return data
            
        try:
            if compression_method == 'ZLIB':
                # ZLIB levels: 0-9 (0=no compression, 9=best compression)
                zlib_level = min(max(level // 3, 0), 9)
                return zlib.compress(data, level=zlib_level)
                
            elif compression_method == 'ZSTD':
                # ZSTD levels: 1-22
                zstd_level = min(max(level, 1), 22)
                return ZstdCompressor(level=zstd_level).compress(data)
                
            elif compression_method == 'ZSTD_DICT' and zstd_dict:
                zstd_level = min(max(level, 1), 22)
                return ZstdCompressor(level=zstd_level, dict_data=zstd_dict).compress(data)
                
        except Exception as e:
            console.print(f"[red]⚠️ Compression failed: {e}")
            
        return data
    
    @staticmethod
    def find_optimal_compression(data: bytes, target_size: int, compression_method: str, 
                                zstd_dict=None, max_level=22) -> tuple[bytes, int, bool]:
        """
        Find the best compression level that fits within target size
        Returns: (compressed_data, level_used, success)
        """
        if compression_method == 'NONE':
            if len(data) <= target_size:
                return data, -1, True
            return data, -1, False
            
        # Try compression levels from highest to lowest
        for level in range(max_level, 0, -1):
            compressed = CompressionManager.compress_block(data, compression_method, level, zstd_dict)
            if compressed and len(compressed) <= target_size:
                return compressed, level, True
                
        # Try level 1 as last resort
        compressed = CompressionManager.compress_block(data, compression_method, 1, zstd_dict)
        if compressed and len(compressed) <= target_size:
            return compressed, 1, True
            
        return data, -1, False

# ==================== MAIN PAK FILE CLASS ====================
class PakCrypto:
    class _LCG:
        def __init__(self, seed: int):
            self.state = seed
        def next(self) -> int:
            MASK_32 = 4294967295
            MSB_1 = 2147483648
            def wrap(x: int) -> int:
                x &= MASK_32
                if not x & MSB_1:
                    return x
                else:
                    return (x + MSB_1 & MASK_32) - MSB_1
            x1 = wrap(1103515245 * self.state)
            self.state = wrap(x1 + 12345)
            x2 = wrap(x1 + 77880) if self.state < 0 else self.state
            return (x2 >> 16 & MASK_32) % 32767
    @staticmethod
    def zuc_keystream() -> list[int]:
        zuc = gmalg.ZUC(const.ZUC_KEY, const.ZUC_IV)
        return [struct.unpack('>I', zuc.generate())[0] for _ in range(16)]
    @staticmethod
    def _xorxor(buffer, x) -> bytes:
        return bytes((buffer[i] ^ x[i % len(x)] for i in range(len(buffer))))
    @staticmethod
    def _hashhash(buffer, n: int) -> bytes:
        result = bytes()
        for i in range(math.ceil(n / SHA1.digest_size)):
            result += SHA1.new(buffer).digest()
        if len(result) >= n:
            result = result[:n]
            return result
        else:
            result += b'\x00' * (n - len(result))
            return result
    @staticmethod
    def _meowmeow(buffer) -> bytes:
        def unpad(x):
            skip = 1 + next((i for i in range(len(x)) if x[i]!= 0))
            return x[skip:]
        if len(buffer) < 43:
            return bytes()
        else:
            x1 = buffer[1:][:SHA1.digest_size]
            x2 = buffer[SHA1.digest_size + 1:]
            x1 = PakCrypto._xorxor(x1, PakCrypto._hashhash(x2, len(x1)))
            x2 = PakCrypto._xorxor(x2, PakCrypto._hashhash(x1, len(x2)))
            part1, m = (x2[:SHA1.digest_size], x2[SHA1.digest_size:])
            if part1!= SHA1.new(b'\x00' * SHA1.digest_size).digest():
                return bytes()
            else:
                return unpad(m)
    @staticmethod
    def rsa_extract(signature: bytes, modulus: bytes) -> bytes:
        c = int.from_bytes(signature, 'little')
        n = int.from_bytes(modulus, 'little')
        e = 65537
        m = pow(c, e, n).to_bytes(256, 'little').rstrip(b'\x00')
        return PakCrypto._meowmeow(Misc.pad_to_n(m, 4))
    @staticmethod
    def _decrypt_simple1(ciphertext) -> bytes:
        return bytes((x ^ const.SIMPLE1_DECRYPT_KEY for x in ciphertext))
    @staticmethod
    def _decrypt_simple2(ciphertext) -> bytes:
        class RollingKey:
            def __init__(self, initial_value: int):
                self._value = initial_value
            def update(self, x: int) -> int:
                self._value ^= x
                return self._value
        assert len(ciphertext) % const.SIMPLE2_BLOCK_SIZE == 0
        initial_key, = struct.unpack('<I', const.SIMPLE2_DECRYPT_KEY)
        rolling_key = RollingKey(initial_key)
        plaintext = (struct.pack('<I', rolling_key.update(x)) for x in struct.unpack(f'<{len(ciphertext) // 4}I', ciphertext))
        return bytes(it.chain.from_iterable(plaintext))
    @staticmethod
    @lru_cache(maxsize=1)
    def _derive_sm4_key(file_path: PurePath, encryption_method: int) -> bytes:
        part1 = file_path.stem.lower()
        if encryption_method == const.EM_SM4_2:
            secret = const.SM4_SECRET_2
        else:
            if encryption_method == const.EM_SM4_4:
                secret = const.SM4_SECRET_4
            else:
                index = (encryption_method - const.EM_SM4_NEW_BASE) % len(const.SM4_SECRET_NEW)
                secret = f'{const.SM4_SECRET_NEW[index]}{encryption_method}'
        return SHA1.new(str(part1 + secret).encode()).digest()[:SM4.key_length()]
    @staticmethod
    @lru_cache(maxsize=1)
    def _sm4_context_for_key(key: bytes) -> SM4:
        return SM4(key)
    @staticmethod
    def _decrypt_sm4(ciphertext, file_path: PurePath, encryption_method: int) -> bytes:
        assert len(ciphertext) % SM4.block_length() == 0
        key = PakCrypto._derive_sm4_key(file_path, encryption_method)
        sm4 = PakCrypto._sm4_context_for_key(key)
        return bytes(it.chain.from_iterable((sm4.decrypt(x) for x in it.batched(ciphertext, SM4.block_length()))))
    @staticmethod
    def decrypt_index(ciphertext, pak_info: TencentPakInfo) -> bytes:
        if pak_info.version > 7:
            key = PakCrypto.rsa_extract(pak_info.packed_key, const.RSA_MOD_1)
            iv = PakCrypto.rsa_extract(pak_info.packed_iv, const.RSA_MOD_1)
            assert len(key) == 32 and len(iv) == 32
            aes = AES.new(key, MODE_CBC, iv[:16])
            return unpad(aes.decrypt(ciphertext), AES.block_size)
        else:
            return bytes(PakCrypto._decrypt_simple1(ciphertext))
    @staticmethod
    def _is_simple1_method(encryption_method: int) -> bool:
        return encryption_method == const.EM_SIMPLE1
    @staticmethod
    def _is_simple2_method(encryption_method: int) -> bool:
        return encryption_method == const.EM_SIMPLE2
    @staticmethod
    def _is_sm4_method(encryption_method: int) -> bool:
        return encryption_method == const.EM_SM4_2 or encryption_method == const.EM_SM4_4 or encryption_method & const.EM_SM4_NEW_MASK!= 0
    @staticmethod
    def align_encrypted_content_size(n: int, encryption_method: int) -> int:
        if PakCrypto._is_simple2_method(encryption_method):
            return Misc.align_up(n, const.SIMPLE2_BLOCK_SIZE)
        else:
            if PakCrypto._is_sm4_method(encryption_method):
                return Misc.align_up(n, SM4.block_length())
            else:
                return n

    @staticmethod
    def decrypt_block(ciphertext, file: PurePath, encryption_method: int) -> bytes:
        if encryption_method == 17:
            return ciphertext
        else:
            if PakCrypto._is_simple1_method(encryption_method):
                return PakCrypto._decrypt_simple1(ciphertext)
            else:
                if PakCrypto._is_simple2_method(encryption_method):
                    return PakCrypto._decrypt_simple2(ciphertext)
                else:
                    if PakCrypto._is_sm4_method(encryption_method):
                        return PakCrypto._decrypt_sm4(ciphertext, file, encryption_method)
                    else:
                        assert False
    @staticmethod
    @lru_cache(maxsize=33)
    def generate_block_indices(n: int, encryption_method: int) -> list[int]:
        if not PakCrypto._is_sm4_method(encryption_method):
            return list(range(n))
        else:
            permutation = []
            lcg = PakCrypto._LCG(n)
            while len(permutation)!= n:
                x = lcg.next() % n
                if x not in permutation:
                    permutation.append(x)
            inverse = [0] * len(permutation)
            for i, x in enumerate(permutation):
                inverse[x] = i
            return inverse
    @staticmethod
    def _encrypt_simple1(plaintext: bytes) -> bytes:
        return bytes((b ^ const.SIMPLE1_DECRYPT_KEY for b in plaintext))
    @staticmethod
    def _encrypt_simple2(plaintext: bytes) -> bytes:
        padded = Misc.pad_to_n(plaintext, const.SIMPLE2_BLOCK_SIZE)
        assert len(padded) % const.SIMPLE2_BLOCK_SIZE == 0
        initial_key, = struct.unpack('<I', const.SIMPLE2_DECRYPT_KEY)
        key_state = initial_key
        cipher_words = []
        plain_words = struct.unpack(f'<{len(padded) // 4}I', padded)
        for plain_word in plain_words:
            cipher_word = plain_word ^ key_state
            key_state = plain_word
            cipher_words.append(cipher_word)
        return struct.pack(f'<{len(cipher_words)}I', *cipher_words)
    @staticmethod
    def _encrypt_sm4(plaintext: bytes, file_path: PurePath, encryption_method: int) -> bytes:
        padded = Misc.pad_to_n(plaintext, SM4.block_length())
        key = PakCrypto._derive_sm4_key(file_path, encryption_method)
        sm4 = PakCrypto._sm4_context_for_key(key)
        encrypted = bytearray()
        for i in range(0, len(padded), SM4.block_length()):
            block = padded[i:i + SM4.block_length()]
            encrypted.extend(sm4.encrypt(block))
        return bytes(encrypted)
    @staticmethod
    def encrypt_block(plaintext: bytes, file: PurePath, encryption_method: int) -> bytes:
        if encryption_method == 17:
            return plaintext
        else:
            if PakCrypto._is_simple1_method(encryption_method):
                return PakCrypto._encrypt_simple1(plaintext)
            else:
                if PakCrypto._is_simple2_method(encryption_method):
                    return PakCrypto._encrypt_simple2(plaintext)
                else:
                    if PakCrypto._is_sm4_method(encryption_method):
                        return PakCrypto._encrypt_sm4(plaintext, file, encryption_method)
                    else:
                        assert False
    @staticmethod
    def encrypt_index(plaintext: bytes, pak_info: TencentPakInfo) -> bytes:
        keystream = PakCrypto.zuc_keystream()
        key = struct.pack('<5I', *keystream[4:][:5])
        if len(plaintext) < len(key):
            plaintext = plaintext + b'\x00' * (len(key) - len(plaintext))
        else:
            if len(plaintext) > len(key):
                key = (key * (len(plaintext) // len(key) + 1))[:len(plaintext)]
        return bytes((a ^ b for a, b in zip(plaintext, key)))
    @staticmethod
    def stat():
        print(PakCrypto._derive_sm4_key.cache_info())
        print(PakCrypto._sm4_context_for_key.cache_info())

class PakCompression:
    @staticmethod
    @lru_cache(maxsize=33)
    def _zstd_decompressor(dict: ZstdCompressionDict | bytes | None) -> ZstdDecompressor:
        if isinstance(dict, bytes):
            dict = ZstdCompressionDict(dict, DICT_TYPE_AUTO)
        return ZstdDecompressor(dict)
    @staticmethod
    def zstd_dictionary(dict_data) -> ZstdCompressionDict:
        return ZstdCompressionDict(dict_data, DICT_TYPE_AUTO)
    @staticmethod
    def decompress_block(block, dict: ZstdCompressionDict | bytes | None, compression_method: int) -> bytes:
        if compression_method == const.CM_ZLIB:
            return zlib.decompress(block)
        else:
            if compression_method == const.CM_ZSTD or compression_method == const.CM_ZSTD_DICT:
                if compression_method!= const.CM_ZSTD_DICT:
                    dict = None
                return PakCompression._zstd_decompressor(dict).decompress(block)
            else:
                assert False

class TencentPakFile:
    def __init__(self, file_path: PurePath, is_od=False):
        self._file_path = file_path

        with open(file_path, 'rb') as file:
            self._file_content = memoryview(file.read())

        self._is_od = is_od
        self._mount_point = PurePath()
        self._is_zstd_with_dict = 'zsdic' in str(self._file_path)
        self._zstd_dict = None

        self._files = []
        self._index: dict[PurePath, dict[str, TencentPakEntry]] = {}

        # Pak info + crypto metadata
        self._pak_info = TencentPakInfo(self._file_content, PakCrypto.zuc_keystream())

        self._verify_stem_hash()
        self._tencent_load_index()

    # ---------- header / index loading ----------

    def _verify_stem_hash(self) -> None:
        if not self._is_od and self._pak_info.version >= 9:
            # crc32 over UTF-32LE stem, same as tool.py
            assert self._pak_info.stem_hash == zlib.crc32(self._file_path.stem.encode('utf-32le'))

    def _tencent_load_index(self) -> None:
        index_data = self._file_content[self._pak_info.index_offset:][:self._pak_info.index_size]

        if self._pak_info.index_encrypted:
            index_data = PakCrypto.decrypt_index(index_data, self._pak_info)

        self._verify_index_hash(index_data)
        self._load_index(index_data)

    def _verify_index_hash(self, index_data) -> None:
        expected_hash = self._pak_info.index_hash

        # For Tencent versions >= 8, index hash is also stored RSA-wrapped;
        # this assert mirrors original behavior.
        if not self._is_od and self._pak_info.version >= 8:
            assert expected_hash == PakCrypto.rsa_extract(self._pak_info.packed_index_hash, const.RSA_MOD_2)

        # Finally, compare against SHA1(index_data)
        assert expected_hash == SHA1.new(index_data).digest()

    @staticmethod
    def _construct_mount_point(mount_point: str) -> PurePath:
        result = PurePath()
        for part in PurePath(mount_point).parts:
            if part != '..':
                result /= part
        return result

    # ---------- content peeking helpers ----------

    def _peek_content(self, offset: int, size: int, encryption_method: int) -> memoryview:
        size = PakCrypto.align_encrypted_content_size(size, encryption_method)
        return self._file_content[offset:][:size]

    def _peek_block_content(self, block: PakCompressedBlock, encryption_method: int) -> memoryview:
        size = PakCrypto.align_encrypted_content_size(block.end - block.start, encryption_method)
        return self._file_content[block.start:][:size]

    # ---------- ZSTD dictionary handling ----------

    def _construct_zstd_dict(self, dict_entry: TencentPakEntry) -> None:
        assert not self._zstd_dict
        assert not dict_entry.encrypted
        assert dict_entry.compression_method == const.CM_NONE

        reader = Reader(self._peek_content(dict_entry.offset, dict_entry.size, 0))
        dict_size = reader.u8()
        _ = reader.u4()
        assert dict_size == reader.u4()
        dict_data = reader.s(dict_size)

        # Ensure dict_data is bytes, not tuple
        if isinstance(dict_data, tuple):
            dict_data = dict_data[0] if dict_data else b''
        
        # Wrap in ZstdCompressionDict for proper usage
        self._zstd_dict = ZstdCompressionDict(dict_data, dict_type=DICT_TYPE_AUTO)

    # ---------- index parsing ----------

    def _load_index(self, index_data) -> None:
        assert not self._pak_info.version <= 10

        reader = Reader(index_data)
        self._mount_point = self._construct_mount_point(reader.string())
        self._files = [TencentPakEntry(reader, self._pak_info.version) for _ in range(reader.u4())]

        for _ in range(reader.u8()):
            dir_path = PurePath(reader.string())
            e = {reader.string(): self._files[~reader.i4()] for _ in range(reader.u8())}

            # Special zstd dictionary pak
            if self._is_zstd_with_dict and dir_path.name == 'zstddic':
                assert len(e) == 1
                self._construct_zstd_dict(e[[*e.keys()][0]])
            else:
                self._index.update({PurePath(dir_path): e})

    # ---------- core file write ----------

    def _write_to_disk(self, file_path: PurePath, entry: TencentPakEntry) -> None:
        if entry.encrypted and entry.encryption_method == 17:
            print(f'   ⚠️ Skipping {file_path.name} - EM_UNKNOWN_17 (unsupported encryption)')
            return

        encryption_method = entry.encryption_method
        compression_method = entry.compression_method

        # OPTIMIZATION: Removed print statement for speed

        with open(file_path, 'wb') as file:
            # Uncompressed file
            if compression_method == const.CM_NONE:
                data = self._peek_content(entry.offset, entry.size, encryption_method)

                if entry.encrypted:
                    data = PakCrypto.decrypt_block(data, file_path, encryption_method)

                file.write(data)
                return

            # Compressed file: iterate blocks in logical order
            for x in PakCrypto.generate_block_indices(len(entry.compressed_blocks), encryption_method):
                data = self._peek_block_content(entry.compressed_blocks[x], encryption_method)

                if entry.encrypted:
                    data = PakCrypto.decrypt_block(data, file_path, encryption_method)

                data = PakCompression.decompress_block(data, self._zstd_dict, compression_method)
                file.write(data)

    # ---------- UNPACK + MANIFEST (real-time) ----------

    def dump(self, out_path: PurePath, use_block_splitting: bool = False) -> None:
        """Enhanced dump with manifest generation - OPTIMIZED FOR SPEED
        
        Args:
            out_path: Output directory path
            use_block_splitting: If True, extract files as separate .block_N files (for easier editing)
        """
        # Store the base output path (WITHOUT mount point) for manifest
        base_out_path = Path(out_path)
        
        # Honor mount point for file extraction
        out_path = base_out_path / self._mount_point
        
        # Create a manifest for this PAK (NO real-time writing for speed)
        manifest = ManifestGenerator(self._file_path.name)
        manifest.set_extraction_mode(use_block_splitting)
        
        file_count = 0
        total_files = sum(len(files) for files in self._index.values())

        for dir_path, dir in self._index.items():
            current_out_path = Path(out_path / dir_path)
            if not current_out_path.exists():
                current_out_path.mkdir(parents=True, exist_ok=True)

            for file_name, entry in dir.items():
                file_count += 1
                
                # OPTIMIZATION: Batch progress (every 50 files)
                if file_count % 50 == 1 or file_count == total_files:
                    print(f'📊 Progress: {file_count}/{total_files} files')
                
                file_path = current_out_path / file_name
                full_rel_path = dir_path / file_name  # path inside pak

                # Figure out where the actual data is in the pak
                if entry.compressed_blocks:
                    actual_offset = entry.compressed_blocks[0].start
                    actual_size = entry.compressed_blocks[0].end - entry.compressed_blocks[0].start
                else:
                    actual_offset = entry.offset
                    actual_size = entry.size

                # Actually write file to disk
                if use_block_splitting and entry.compressed_blocks:
                    # Reconstruct full decompressed file in the SAME logical order as normal extraction,
                    # then split sequentially into fixed 64KB chunks (+ remainder as last chunk).
                    try:
                        encryption_method = entry.encryption_method
                        compression_method = entry.compression_method

                        plain_parts: list[bytes] = []
                        for x in PakCrypto.generate_block_indices(len(entry.compressed_blocks), encryption_method):
                            block = entry.compressed_blocks[x]
                            block_data = self._peek_block_content(block, encryption_method)

                            if entry.encrypted:
                                block_data = PakCrypto.decrypt_block(block_data, file_path, encryption_method)

                            block_plain = PakCompression.decompress_block(block_data, self._zstd_dict, compression_method)
                            plain_parts.append(block_plain)

                        full_plain = b''.join(plain_parts)

                        # Safety: trim to declared uncompressed size (avoids padding / over-read)
                        if entry.uncompressed_size and len(full_plain) > entry.uncompressed_size:
                            full_plain = full_plain[:entry.uncompressed_size]

                        # Always split into 64KB sequential blocks (and remainder as last)
                        block_size = 64 * 1024

                        stem = file_path.stem
                        ext = file_path.suffix

                        block_idx = 0
                        for off in range(0, len(full_plain), block_size):
                            chunk = full_plain[off:off + block_size]
                            block_file = file_path.parent / f'{stem}_block_{block_idx}{ext}'
                            block_file.write_bytes(chunk)

                            manifest.add_block_file_entry(full_rel_path, block_idx, len(chunk), entry)
                            block_idx += 1

                    except Exception as e:
                        print(f'Failed block-split of {file_name}: {e}')
                else:
                    # Normal full-file write
                    self._write_to_disk(file_path, entry)
                    # Only add to manifest for full files
                    manifest.add_file_entry(full_rel_path, entry, actual_offset, actual_size)

        # Final save with summary - save to BASE path, not the mount point subfolder
        print('💾 Finalizing manifest...')
        manifest.save(base_out_path)
        
        # Create 'edited' folder automatically for user convenience
        edited_folder = base_out_path / 'edited'
        if not edited_folder.exists():
            edited_folder.mkdir(parents=True, exist_ok=True)
            print(f'📁 Created "edited" folder: {edited_folder}')
            print('   💡 Place your modified files here for repacking')

    # ---------- REPACK (uses manifest.json) ----------

    def repack(self, input_folder: PurePath, output_pak: PurePath) -> None:
        logger = RepackLogger()
        # Track which PAK entries we modified so we can verify them after writing
        modified_targets: list[tuple[PurePath, TencentPakEntry]] = []

        print(f'🔄 Repacking from {input_folder} to {output_pak}')
        input_path = Path(input_folder)
        
        # Define unpacked_folder as the parent directory containing both 'extracted' and 'edited' folders
        unpacked_folder = input_path.parent

        if not input_path.exists():
            raise FileNotFoundError(f'Input folder not found: {input_folder}')
        else:
            manifest_reader = None
            manifest_path = input_path.parent / 'manifest.json'

            if manifest_path.exists():
                try:
                    manifest_reader = ManifestReader(manifest_path)
                except Exception as e:
                    print(f'⚠️ Manifest error: {e}')

            print('📋 Copying original pak...')

            temp_pak = Path(str(output_pak) + '.tmp')
            shutil.copy2(self._file_path, temp_pak)
            print('✅ Base copied')

            # Get all files from the edited folder ONLY
            mod_files = []
            if input_path.exists():
                # Collect all relevant files
                for item in input_path.rglob('*'):
                    if item.is_file():
                        # Check if it's a file type we care about
                        if item.suffix.lower() in ['.uasset', '.uexp', '.ubulk', '.umap']:
                            mod_files.append(item)
                
                print(f"🔍 Found {len(mod_files)} files in edited folder")
                
                # Debug: Show what we found with full paths
                if mod_files:
                    print("   Files found with full paths:")
                    for i, f in enumerate(mod_files[:10]):  # Show first 10
                        try:
                            rel_path = f.relative_to(input_path)
                            print(f"   {i+1}. {rel_path} ({f.stat().st_size:,} bytes)")
                        except:
                            print(f"   {i+1}. {f.name} ({f.stat().st_size:,} bytes)")
                    if len(mod_files) > 10:
                        print(f"   ... and {len(mod_files) - 10} more files")
                else:
                    print("   ⚠️ No files found in edited folder!")
            else:
                print(f"❌ Edited folder does not exist: {input_path}")
                temp_pak.unlink(missing_ok=True)
                return

            # Build block file lookup from manifest - using full paths
            block_file_lookup = {}  # full_path_in_edited_folder -> block_info
            if manifest_reader:
                for block_filename, block_info in manifest_reader.block_files.items():
                    parent_file = block_info.get('parent_file')
                    if parent_file:
                        # Create the expected path in the edited folder
                        # parent_file is like "ShadowTrackerExtra/Content/MultiRegion/Content/IN/CSV/Item.uasset"
                        parent_dir = Path(parent_file).parent
                        block_filename = block_info.get('extracted_filename')
                        expected_relative_path = str(parent_dir / block_filename).replace('\\', '/')
                        
                        block_file_lookup[expected_relative_path] = {
                            'parent': parent_file,
                            'block_index': block_info.get('block_index', 0),
                            'block_size': block_info.get('block_size', 0),
                            'extracted_filename': block_filename
                        }
            
            # Group block files by parent based on actual file paths
            block_groups_by_parent = {}  # parent_pak_path -> [(block_index, filepath, size)]
            
            for mod_file in mod_files:
                # Get the relative path from edited folder
                try:
                    rel_path_str = str(mod_file.relative_to(input_path)).replace('\\', '/')
                    
                    # Check if this is a block file by looking up its relative path
                    if rel_path_str in block_file_lookup:
                        info = block_file_lookup[rel_path_str]
                        parent = info['parent']
                        
                        if parent not in block_groups_by_parent:
                            block_groups_by_parent[parent] = []
                        
                        block_groups_by_parent[parent].append((
                            info['block_index'],
                            mod_file,
                            info['block_size']
                        ))
                        continue
                    
                    # Also check if filename has _block_ pattern (for manual edits)
                    filename = mod_file.name
                    if '_block_' in filename:
                        # Try to match by reconstructing the parent path from directory structure
                        # Get the directory path relative to edited folder
                        rel_dir = str(mod_file.parent.relative_to(input_path)).replace('\\', '/')
                        
                        # Look for files in manifest that have this directory structure
                        for parent_path, file_info in manifest_reader.manifest.get('files', {}).items():
                            # Get the directory of the parent file in manifest
                            parent_dir = str(Path(parent_path).parent).replace('\\', '/')
                            
                            # Check if this matches and the file was extracted as blocks
                            if parent_dir == rel_dir and file_info.get('extracted_as_blocks'):
                                # Extract block index from filename
                                try:
                                    block_index = int(filename.split('_block_')[1].split('.')[0])
                                except (ValueError, IndexError):
                                    block_index = 0
                                
                                if parent_path not in block_groups_by_parent:
                                    block_groups_by_parent[parent_path] = []
                                
                                block_groups_by_parent[parent_path].append((
                                    block_index,
                                    mod_file,
                                    mod_file.stat().st_size
                                ))
                                break
                            
                except ValueError:
                    # File not in input_path (shouldn't happen)
                    continue
            
            # Sort blocks within each group
            for parent in block_groups_by_parent:
                block_groups_by_parent[parent].sort(key=lambda x: x[0])
            
            # Filter out block files from mod_files list (they'll be processed separately)
            regular_mod_files = []
            for f in mod_files:
                # Get relative path
                try:
                    rel_path_str = str(f.relative_to(input_path)).replace('\\', '/')
                    # Check if this file is in block_file_lookup or has _block_ pattern
                    if rel_path_str in block_file_lookup or '_block_' in f.name:
                        # It's a block file, skip from regular processing
                        continue
                except ValueError:
                    pass
                regular_mod_files.append(f)
            
            mod_files = regular_mod_files
            
            # Show what we found
            if block_groups_by_parent:
                console.print(f'\n📦 Found {len(block_groups_by_parent)} files with block-based extraction:')
                for parent, blocks in block_groups_by_parent.items():
                    parent_name = Path(parent).name
                    console.print(f'   • {parent_name}: {len(blocks)} block(s) at {parent}')
                    for block_idx, block_file, block_size in blocks[:3]:  # Show first 3 blocks
                        try:
                            rel_path = block_file.relative_to(input_path)
                            console.print(f'      - Block {block_idx}: {rel_path} ({block_size:,} bytes)')
                        except:
                            console.print(f'      - Block {block_idx}: {block_file.name} ({block_size:,} bytes)')
                    if len(blocks) > 3:
                        console.print(f'      ... and {len(blocks) - 3} more blocks')
            
            if not mod_files and not block_groups_by_parent:
                print('\n⚠️ No files found to repack')
                temp_pak.unlink(missing_ok=True)
                logger.print_summary()
                return
            else:
                total_files = len(mod_files) + len(block_groups_by_parent)
                print(f'\n📝 Found {total_files} files to process ({len(mod_files)} regular, {len(block_groups_by_parent)} block-based)\n')

                work_items = []

                # ============================================================
                # Process regular files (not block files)
                # ============================================================
                for mod_file in mod_files:
                    mod_name = mod_file.name
                    print(f'🔍 Processing regular file: {mod_name}')
                    
                    try:
                        mod_bytes = mod_file.read_bytes()
                    except Exception as e:
                        print(f'   ❌ Error reading file: {e}')
                        continue
                        
                    print(f'   📊 File size: {len(mod_bytes):,} bytes')

                    entries: list[tuple[PurePath, TencentPakEntry]] = []

                    # Use the relative path from input_folder to match PAK structure
                    try:
                        # Get relative path from edited folder
                        rel_path = mod_file.relative_to(input_path)
                        # Convert to string with forward slashes
                        rel_path_str = str(rel_path).replace('\\', '/')
                        print(f'   📁 Relative path: {rel_path_str}')
                        
                        # Use the full path for logging to avoid confusion with duplicate filenames
                        display_name = rel_path_str  # Use full path instead of just filename
                        
                        # Look for this exact path in the manifest
                        if manifest_reader:
                            manifest_info = manifest_reader.find_file_info(rel_path_str, quiet_on_exact_match=True)
                            if manifest_info:
                                # Found by relative path - great!
                                print(f'   ✅ Matched by relative path in manifest')
                                # Now we need to find the actual PAK entry
                                for dp, df in self._index.items():
                                    for fn, ent in df.items():
                                        full_pak_path = str(dp / fn).replace('\\', '/')
                                        if full_pak_path == rel_path_str:
                                            entries.append((dp / fn, ent))
                                            break
                                    if entries:
                                        break
                    
                    except ValueError:
                        # File not in input_path (shouldn't happen)
                        display_name = mod_name  # Fallback to filename only
                    
                    # If display_name wasn't set (shouldn't happen), use filename
                    if 'display_name' not in locals():
                        display_name = mod_name

                    # Fallback: if no path match, try filename-only match
                    if not entries:
                        for dp, df in self._index.items():
                            for fn, ent in df.items():
                                if fn == mod_name:
                                    full_pak_path = dp / fn
                                    pak_parts = full_pak_path.parts
                                    display_path = '/'.join(pak_parts[-min(4, len(pak_parts)):])
                                    print(f'   ⚠️ Warning: filename-only match: {display_path}')
                                    entries.append((full_pak_path, ent))
                    
                    # Now print manifest details for the matched entry
                    if manifest_reader and entries:
                        matched_pak_path = str(entries[0][0])
                        manifest_reader.print_file_details(matched_pak_path, quiet_on_exact_match=True)

                    if not entries:
                        print('   ⚠️ No match')
                        logger.log_failure(display_name, 'No matching PAK entry', {})
                        continue
                    
                    if len(entries) > 1:
                        print(f'   ⚠️ Warning: Found {len(entries)} potential matches for {mod_name}')
                        print(f'   💡 Tip: Organize your files in subfolders matching the PAK structure to ensure correct matching')
                        for idx, (epath, eentry) in enumerate(entries):
                            pak_path_display = '/'.join(epath.parts[-min(4, len(epath.parts)):])
                            print(f'      {idx+1}. {pak_path_display} (uncompressed: {eentry.uncompressed_size:,} bytes)')
                        print(f'   ℹ️ Will attempt repacking with the first valid match')
                    
                    # Early size validation
                    if entries:
                        matching_size_found = False
                        for epath, eentry in entries:
                            if eentry.uncompressed_size == len(mod_bytes):
                                matching_size_found = True
                                break
                        
                        if not matching_size_found:
                            print(f'   ⚠️ WARNING: Your file size ({len(mod_bytes):,} bytes) doesn\'t match any PAK entry!')
                            print(f'   Expected sizes for entries with this filename:')
                            for epath, eentry in entries:
                                pak_path_display = '/'.join(epath.parts[-min(4, len(epath.parts)):])
                                print(f'      • {pak_path_display}: {eentry.uncompressed_size:,} bytes')
                            print(f'   ℹ️ This usually means:')
                            print(f'      1. You\'re modifying a different version of the file than what\'s in the PAK')
                            print(f'      2. The file has been edited beyond what the original slots can accommodate')
                            print(f'      3. There are multiple files with this name and you need better path matching')

                    success = False

                    # Create per-file block logger
                    block_logger = BlockLogger(display_name)

                    for epath, eentry in entries:
                        if eentry.encrypted and eentry.encryption_method == 17:
                            print('   ⚠️ Skipping entry - EM_UNKNOWN_17 (unsupported encryption)')
                            continue

                        blocks = eentry.compressed_blocks
                        compression_method = eentry.compression_method
                        encryption_method = eentry.encryption_method if eentry.encrypted else 0

                        block_size = eentry.compression_block_size

                        if not blocks:
                            # Uncompressed (rare), treat as single block
                            slot = eentry.size
                            print(f'   📦 Uncompressed single slot: {slot:,} bytes')

                            if len(mod_bytes) > slot:
                                print(f'   ❌ Mod too large: {len(mod_bytes):,} > {slot:,}')
                                logger.log_failure(display_name, 'Mod too large for slot', {'mod_size': len(mod_bytes), 'slot': slot})
                                continue

                            result = mod_bytes  # raw bytes; padding/encryption handled below
                            level_used = -1  # No compression
                            comp_method_str = 'NONE'

                            if eentry.encrypted:
                                cipher_slot = PakCrypto.align_encrypted_content_size(slot, encryption_method)
                                if len(result) > cipher_slot:
                                    raise ValueError(f'Entry data {len(result)} does not fit cipher slot {cipher_slot} (slot {slot}) for encryption method {encryption_method}')
                                padded_plain = result + b'\x00' * (cipher_slot - len(result))
                                cipher = PakCrypto.encrypt_block(padded_plain, epath, encryption_method)
                                if len(cipher) != cipher_slot:
                                    raise ValueError(f'Encrypted entry size mismatch: got {len(cipher)} bytes, expected {cipher_slot}')
                                result = cipher + b'\x00' * (slot - cipher_slot)

                            work_items.append((epath, [(eentry.offset, result)], False))
                            modified_targets.append((epath, eentry))
                            block_logger.add_block(0, len(mod_bytes), len(result), comp_method_str, level_used, True, eentry.offset, eentry.offset + slot)
                            # Log success for uncompressed single-block file
                            logger.log_success(display_name, slot, slot)
                            success = True
                            break

                        # Single-block
                        elif len(blocks) == 1:
                            block = blocks[0]
                            slot = block.end - block.start
                            
                            comp_method_str = {0: 'NONE', 1: 'ZLIB', 6: 'ZSTD', 8: 'ZSTD_DICT'}.get(compression_method, 'UNKNOWN')
                            enc_method_str = {0: 'NONE', 2: 'AES', 40: 'SM4'}.get(encryption_method, 'UNKNOWN')
                            
                            print(f'   ╔═══════════════════════════════════════════════════════════════════════════════')
                            print(f'   ║ 📄 SINGLE-BLOCK FILE COMPRESSION')
                            print(f'   ╠═══════════════════════════════════════════════════════════════════════════════')
                            print(f'   ║ File: {mod_name}')
                            print(f'   ║ Modified size: {len(mod_bytes):,} bytes')
                            print(f'   ║ Slot size: {slot:,} bytes')
                            print(f'   ║ Compression: {comp_method_str} (method {compression_method})')
                            print(f'   ║ Encryption: {enc_method_str} (method {encryption_method})')
                            print(f'   ╚═══════════════════════════════════════════════════════════════════════════════')

                            result = None
                            level_used = -1

                            # ALWAYS RECOMPRESS - No reuse logic
                            best_compressed = None
                            best_size = float('inf')
                            best_level = -1
                            
                            # Determine compression method details
                            if compression_method == const.CM_ZLIB:
                                comp_method_name = "ZLIB"
                                max_level = 9
                                level_step = 1  # Try every level
                            elif compression_method in [const.CM_ZSTD, const.CM_ZSTD_DICT]:
                                comp_method_name = "ZSTD" if compression_method == const.CM_ZSTD else "ZSTD_DICT"
                                max_level = 22
                                level_step = 1  # Try every level for better fit
                            else:
                                comp_method_name = "UNKNOWN"
                                max_level = 9
                                level_step = 1
                            
                            print(f'   🔧 Compressing with {comp_method_name} (max level: {max_level}, trying all levels)')
                            print(f'   📏 Original: {len(mod_bytes):,} bytes, Target slot: {slot:,} bytes')
                            
                            # Calculate usable slot size (accounting for encryption overhead if needed)
                            usable_slot = slot
                            if eentry.encrypted:
                                usable_slot = PakCrypto.align_encrypted_content_size(slot, encryption_method)
                            
                            attempts = 0
                            for lvl in range(max_level, 0, -level_step):
                                attempts += 1
                                comp = None

                                try:
                                    if compression_method == const.CM_ZLIB:
                                        actual_level = min(lvl, 9)
                                        comp = zlib.compress(mod_bytes, level=actual_level)
                                        lvl_display = actual_level
                                    elif compression_method == const.CM_ZSTD:
                                        comp = ZstdCompressor(level=lvl).compress(mod_bytes)
                                        lvl_display = lvl
                                    elif compression_method == const.CM_ZSTD_DICT and self._zstd_dict is not None:
                                        comp = ZstdCompressor(level=lvl, dict_data=self._zstd_dict).compress(mod_bytes)
                                        lvl_display = lvl
                                    else:
                                        print(f'   ❌ Unknown compression method: {compression_method}')
                                        break

                                    if comp:
                                        comp_size = len(comp)
                                        ratio = (comp_size / len(mod_bytes)) * 100
                                        savings = len(mod_bytes) - comp_size
                                        slot_usage = (comp_size / usable_slot) * 100
                                        
                                        fit_status = "✅ FIT" if comp_size <= slot else "❌ TOO BIG"
                                        
                                        print(f'   │ Attempt {attempts}: Level {lvl_display:>2} │ {len(mod_bytes):>8,} → {comp_size:>8,} bytes │ Ratio: {ratio:>6.2f}% │ Saved: {savings:>7,} │ Slot: {slot_usage:>6.2f}% │ {fit_status}')
                                        
                                        if comp_size < best_size:
                                            best_size = comp_size
                                            best_compressed = comp
                                            best_level = lvl_display

                                        if comp_size <= usable_slot:
                                            result = comp
                                            level_used = lvl_display
                                            print(f'   └─> ✅ SUCCESS! Compressed {len(mod_bytes):,} → {comp_size:,} bytes using level {lvl_display} ({slot_usage:.2f}% slot usage)')
                                            break
                                except Exception as e:
                                    print(f'   │ Attempt {attempts}: Level {lvl:>2} │ ⚠️ ERROR: {str(e)}')
                                    continue

                            if result is None:
                                if best_compressed:
                                    overage = best_size - slot
                                    overage_pct = (overage / slot) * 100
                                    print(f'   └─> ❌ FAILED! Best compression: {best_size:,} bytes at level {best_level}')
                                    print(f'       Target slot: {slot:,} bytes')
                                    print(f'       Overage: {overage:,} bytes ({overage_pct:.2f}% over limit)')
                                    print(f'       Tried {attempts} compression levels')
                                logger.log_failure(display_name, 'Compression failed to fit', {'best_size': best_size, 'slot': slot})
                                continue

                            # Store actual compressed size before padding/encryption
                            compressed_size_for_log = len(result)

                            # Always overwrite the full stored slot range (single-block)
                            if eentry.encrypted:
                                cipher_slot = PakCrypto.align_encrypted_content_size(slot, encryption_method)
                                if len(result) > cipher_slot:
                                    raise ValueError(f'Compressed data {len(result)} does not fit cipher slot {cipher_slot} (slot {slot})')
                                padded_plain = result + b'\x00' * (cipher_slot - len(result))
                                cipher = PakCrypto.encrypt_block(padded_plain, epath, encryption_method)
                                if len(cipher) != cipher_slot:
                                    raise ValueError(f'Encrypted block size mismatch: got {len(cipher)} bytes, expected {cipher_slot}')
                                result = cipher + b'\x00' * (slot - cipher_slot)
                                print(f'   🔒 Encrypted with {enc_method_str}: {len(result):,} bytes ({cipher_slot:,} encrypted + {slot - cipher_slot} pad)')
                            else:
                                result = result + b'\x00' * (slot - len(result))

                            # Log actual compressed size, not padded
                            block_logger.add_block(0, len(mod_bytes), compressed_size_for_log, comp_method_str, level_used, True, block.start, block.end)

                            work_items.append((epath, [(block.start, result)], False))
                            modified_targets.append((epath, eentry))
                            # Log success for single-block file
                            logger.log_success(display_name, slot, slot)
                            success = True
                            break

                        # Multi-block (always per-chunk)
                        else:
                            total_slot_size = sum((b.end - b.start for b in blocks))
                            block_size_kb = block_size / 1024
                            total_slot_kb = total_slot_size / 1024
                            mod_size_kb = len(mod_bytes) / 1024
                            
                            comp_method_str = {0: 'NONE', 1: 'ZLIB', 6: 'ZSTD', 8: 'ZSTD_DICT'}.get(compression_method, 'UNKNOWN')
                            enc_method_str = {0: 'NONE', 2: 'AES', 40: 'SM4'}.get(encryption_method, 'UNKNOWN')
                            
                            print(f'   ╔═══════════════════════════════════════════════════════════════════════════════')
                            print(f'   ║ 📦 MULTI-BLOCK FILE COMPRESSION')
                            print(f'   ╠═══════════════════════════════════════════════════════════════════════════════')
                            print(f'   ║ File: {mod_name}')
                            print(f'   ║ Modified size: {len(mod_bytes):,} bytes ({mod_size_kb:.2f} KB)')
                            print(f'   ║ Blocks: {len(blocks)} blocks × {block_size:,} bytes ({block_size_kb:.2f} KB per block)')
                            print(f'   ║ Total slot space: {total_slot_size:,} bytes ({total_slot_kb:.2f} KB)')
                            print(f'   ║ Compression: {comp_method_str} (method {compression_method})')
                            print(f'   ║ Encryption: {enc_method_str} (method {encryption_method})')
                            print(f'   ╚═══════════════════════════════════════════════════════════════════════════════')

                            chunks = list(it.batched(mod_bytes, block_size))
                            # Convert tuples to bytes (it.batched returns tuples)
                            chunks = [bytes(chunk) if isinstance(chunk, tuple) else chunk for chunk in chunks]
                            if len(chunks) > len(blocks):
                                print(f'   ❌ Too many chunks: {len(chunks)} > {len(blocks)} blocks')
                                logger.log_failure(display_name, 'Too many chunks', {'chunks': len(chunks), 'blocks': len(blocks)})
                                continue

                            # IMPORTANT: Some encryption methods (SM4 variants) permute block ordering.
                            # Use the same mapping as dump() so logical chunk i maps to the correct stored block.
                            block_indices = PakCrypto.generate_block_indices(len(blocks), encryption_method)

                            # ========== BLOCK REUSE OPTIMIZATION ==========
                            print(f'   🔍 Analyzing blocks for reuse...')
                            block_reuse_decisions = {}  # idx -> (should_reuse, original_compressed_data)
                            
                            try:
                                # Find the original unpacked file to compare
                                # It should be in: unpacked/{pak_name}/{relative_path}
                                original_file_path = unpacked_folder / str(epath).replace('\\', '/')
                                
                                if not original_file_path.exists():
                                    raise FileNotFoundError(f"Original file not found at: {original_file_path}")
                                
                                # Read original file from disk
                                with open(original_file_path, 'rb') as f:
                                    orig_data = f.read()
                                
                                orig_chunks = list(it.batched(orig_data, block_size))
                                orig_chunks = [bytes(c) if isinstance(c, tuple) else c for c in orig_chunks]
                                
                                unchanged_count = 0
                                changed_count = 0
                                
                                for idx in range(len(chunks)):
                                    # Compare this block with original
                                    if idx < len(orig_chunks) and chunks[idx] == orig_chunks[idx]:
                                        # UNCHANGED - can reuse original compressed block
                                        stored_idx = block_indices[idx] if idx < len(block_indices) else idx
                                        block = blocks[stored_idx]
                                        
                                        # Read the original compressed+encrypted block data from PAK
                                        orig_compressed = self._peek_block_content(block, encryption_method)
                                        
                                        block_reuse_decisions[idx] = (True, orig_compressed)
                                        unchanged_count += 1
                                    else:
                                        # CHANGED - must recompress
                                        block_reuse_decisions[idx] = (False, None)
                                        changed_count += 1
                                
                                print(f'   📊 Block analysis: ✅ {unchanged_count} unchanged (reuse), 🔄 {changed_count} changed (recompress)')
                                
                            except Exception as e:
                                print(f'   ⚠️  Could not analyze blocks: {e}')
                                print(f'   ⚠️  Falling back to recompressing all blocks')
                                # Fallback: recompress everything
                                block_reuse_decisions = {idx: (False, None) for idx in range(len(chunks))}
                            # ========== END BLOCK REUSE OPTIMIZATION ==========

                            compressed_chunks = []
                            all_fit = True
                            comp_method_str = {0: 'NONE', 1: 'ZLIB', 6: 'ZSTD', 8: 'ZSTD_DICT'}.get(compression_method, 'UNKNOWN')

                            for idx, chunk in enumerate(chunks):
                                # idx is the logical chunk index; map to stored block index if needed
                                stored_idx = block_indices[idx] if idx < len(block_indices) else idx
                                block = blocks[stored_idx]
                                slot = block.end - block.start
                                usable_slot = slot
                                if eentry.encrypted:
                                    usable_slot = PakCrypto.align_encrypted_content_size(slot, encryption_method)
                                orig_chunk_size = len(chunk)
                                print(f'      🔄 Block {idx}: {orig_chunk_size:,} bytes → Slot: {slot:,} bytes (must fit)')

                                result = None
                                level_used = -1

                                # ========== CHECK BLOCK REUSE DECISION ==========
                                should_reuse, orig_compressed = block_reuse_decisions.get(idx, (False, None))
                                
                                if should_reuse and orig_compressed:
                                    # Block unchanged - reuse original compressed data
                                    print(f'         ✅ UNCHANGED - Reusing original block ({len(orig_compressed):,} bytes, {(len(orig_compressed)/slot)*100:.1f}% of slot)')
                                    result = orig_compressed
                                    level_used = -1  # Original level
                                    
                                else:
                                    # Block changed - recompress
                                    print(f'         🔧 Compressing block...')

                                    # Recompress
                                    best_compressed = None
                                    best_size = float('inf')
                                    best_level = -1
                                    
                                    # Determine compression method details
                                    if compression_method == const.CM_ZLIB:
                                        comp_method_name = "ZLIB"
                                        max_level = 9
                                        level_step = 1  # Try every level
                                    elif compression_method in [const.CM_ZSTD, const.CM_ZSTD_DICT]:
                                        comp_method_name = "ZSTD" if compression_method == const.CM_ZSTD else "ZSTD_DICT"
                                        max_level = 22
                                        level_step = 1  # Try every level for better fit
                                    else:
                                        comp_method_name = "UNKNOWN"
                                        max_level = 9
                                        level_step = 1
                                    
                                    print(f'         🔧 Compressing with {comp_method_name} (trying levels 22→1)')
                                    
                                    attempts = 0
                                    for lvl in range(max_level, 0, -level_step):
                                        attempts += 1
                                        comp = None

                                        try:
                                            if compression_method == const.CM_ZLIB:
                                                actual_level = min(lvl, 9)
                                                comp = zlib.compress(chunk, level=actual_level)
                                                lvl_display = actual_level
                                            elif compression_method == const.CM_ZSTD:
                                                comp = ZstdCompressor(level=lvl).compress(chunk)
                                                lvl_display = lvl
                                            elif compression_method == const.CM_ZSTD_DICT and self._zstd_dict is not None:
                                                comp = ZstdCompressor(level=lvl, dict_data=self._zstd_dict).compress(chunk)
                                                lvl_display = lvl
                                            else:
                                                print(f'         ❌ Unknown compression method: {compression_method}')
                                                break

                                            if comp:
                                                comp_size = len(comp)
                                                slot_remaining = usable_slot - comp_size
                                                slot_usage = (comp_size / usable_slot) * 100
                                                
                                                fit_status = "✅" if comp_size <= usable_slot else "❌"
                                                
                                                print(f'         │ L{lvl_display:>2} │ {orig_chunk_size:>8,} → {comp_size:>8,} │ Slot: {usable_slot:>8,} ({slot_usage:>6.2f}%) │ Free: {slot_remaining:>7,} │ {fit_status}')
                                                
                                                if comp_size < best_size:
                                                    best_size = comp_size
                                                    best_compressed = comp
                                                    best_level = lvl_display

                                                if comp_size <= usable_slot:
                                                    result = comp
                                                    level_used = lvl_display
                                                    print(f'         └─> ✅ SUCCESS at Level {lvl_display}!')
                                                    break
                                        except Exception as e:
                                            print(f'         │ L{lvl:>2} │ ⚠️ ERROR: {str(e)}')
                                            continue

                                    if result is None:
                                        all_fit = False
                                        if best_compressed:
                                            overage = best_size - slot
                                            overage_pct = (overage / slot) * 100
                                            print(f'         └─> ❌ FAILED! Best: L{best_level} = {best_size:,} bytes (over by {overage:,} bytes / {overage_pct:.2f}%)')
                                        else:
                                            print(f'         └─> ❌ FAILED! No valid compression found')
                                        block_logger.add_block(idx, orig_chunk_size, best_size if best_compressed else orig_chunk_size, comp_method_str, best_level, False, block.start, block.end)
                                        break
                                # END of recompress block
                                
                                # Process the result (either reused or newly compressed)
                                # For reused blocks, result is already compressed+encrypted+padded from original
                                # For newly compressed blocks, we need to encrypt and pad
                                
                                if not should_reuse:
                                    # Newly compressed - need to encrypt and pad
                                    compressed_size_for_log = len(result)  # Store actual compressed size before padding
                                    
                                    if eentry.encrypted:
                                        cipher_slot = PakCrypto.align_encrypted_content_size(slot, encryption_method)
                                        if len(result) > cipher_slot:
                                            raise ValueError(f'Compressed data {len(result)} does not fit cipher slot {cipher_slot} (slot {slot})')
                                        padded_plain = result + b'\x00' * (cipher_slot - len(result))
                                        cipher = PakCrypto.encrypt_block(padded_plain, epath, encryption_method)
                                        if len(cipher) != cipher_slot:
                                            raise ValueError(f'Encrypted block size mismatch: got {len(cipher)} bytes, expected {cipher_slot}')
                                        result = cipher + b'\x00' * (slot - cipher_slot)
                                        print(f'         🔒 Encrypted: {len(result):,} bytes ({cipher_slot:,} encrypted + {slot - cipher_slot} pad)')
                                    else:
                                        # Unencrypted: pad to slot so we don't leave stale trailing bytes
                                        result = result + b'\x00' * (slot - len(result))

                                    # Log the ACTUAL compressed size and usable slot size, not the padded size
                                    block_logger.add_block(idx, orig_chunk_size, compressed_size_for_log, comp_method_str, level_used, True, block.start, block.start + usable_slot)
                                else:
                                    # Reused block - already compressed, encrypted, and padded
                                    # Just log it with original size
                                    block_logger.add_block(idx, orig_chunk_size, len(result), comp_method_str, -1, True, block.start, block.start + usable_slot)
                                
                                compressed_chunks.append((block.start, result))

                            if all_fit:
                                work_items.append((epath, compressed_chunks, True))
                                modified_targets.append((epath, eentry))
                                # For successful repacks, utilization is 100% (slot size / slot size)
                                logger.log_success(display_name, total_slot_size, total_slot_size)
                                success = True
                                break
                            else:
                                print('   ❌ Some blocks failed to fit')
                                logger.log_failure(display_name, 'Block compression failed', {'total_slot': total_slot_size})

                        # Print per-file block summary
                        if blocks:
                            block_logger.print_summary()

                    if not success:
                        print('   ⚠️ Repack failed for all candidates')
                
                # ============================================================
                # Process block-based files
                # ============================================================
                for parent_file_path, blocks_info in block_groups_by_parent.items():
                    print(f'\n🔍 Processing block-based file: {parent_file_path}')
                    console.print(f'   📦 Reassembling from {len(blocks_info)} blocks...')
                    
                    # Find the PAK entry for this parent file
                    parent_entry = None
                    parent_pak_path = None
                    
                    # Look for this file in the pak index
                    for dp, df in self._index.items():
                        for fn, ent in df.items():
                            full_pak_path = str(dp / fn).replace('\\', '/')
                            if full_pak_path == parent_file_path:
                                parent_entry = ent
                                parent_pak_path = dp / fn
                                break
                        if parent_entry:
                            break
                    
                    if not parent_entry:
                        console.print(f'   ❌ No PAK entry found for: {parent_file_path}')
                        logger.log_failure(Path(parent_file_path).name, 'No PAK entry found', {'path': parent_file_path})
                        continue
                    
                    # Get the expected block count from manifest
                    expected_block_count = 0
                    manifest_info = manifest_reader.find_file_info(parent_file_path, quiet_on_exact_match=True)
                    if manifest_info:
                        expected_block_count = manifest_info.get('num_blocks', 0)
                    
                    # Check if we have all expected blocks
                    if expected_block_count > 0 and len(blocks_info) != expected_block_count:
                        console.print(f'   ⚠️ Warning: Found {len(blocks_info)} blocks but expected {expected_block_count}')
                        console.print(f'   ℹ️ Make sure all block files are present in the edited folder')
                        
                        # List missing blocks
                        found_indices = [idx for idx, _, _ in blocks_info]
                        missing_indices = [i for i in range(expected_block_count) if i not in found_indices]
                        if missing_indices:
                            console.print(f'   ❌ Missing blocks: {missing_indices}')
                    
                    # Sort blocks by index
                    blocks_info.sort(key=lambda x: x[0])
                    
                    # Get PAK blocks info
                    pak_blocks = parent_entry.compressed_blocks
                    compression_method = parent_entry.compression_method
                    encryption_method = parent_entry.encryption_method
                    # Some encryption methods (SM4 variants) permute block ordering.
                    # Map logical block indices (block_N) to the stored block indices in the PAK.
                    block_indices = PakCrypto.generate_block_indices(len(pak_blocks), encryption_method)
                    
                    # SMART REUSE: Check each block file against original before assembly
                    block_reuse_decisions = {}  # block_idx -> (should_reuse, original_compressed_data)
                    
                    console.print(f'   🔍 Checking which blocks were actually modified...')
                    reused_count = 0
                    modified_count = 0
                    
                    for block_idx, block_file, expected_size in blocks_info:
                        if block_idx >= len(pak_blocks):
                            console.print(f'   ⚠️ Block {block_idx} index out of range')
                            block_reuse_decisions[block_idx] = (False, None)
                            modified_count += 1
                            continue
                        
                        stored_idx = block_indices[block_idx] if block_idx < len(block_indices) else block_idx
                        pak_block = pak_blocks[stored_idx]
                        
                        try:
                            # Read the block file
                            block_file_data = block_file.read_bytes()
                            
                            # Read original compressed block from PAK
                            orig_raw = self._peek_block_content(pak_block, encryption_method)
                            
                            # Decrypt if needed
                            if parent_entry.encrypted:
                                orig_comp = PakCrypto.decrypt_block(orig_raw, parent_pak_path, encryption_method)
                            else:
                                orig_comp = orig_raw
                            
                            # Decompress original to compare
                            orig_plain = PakCompression.decompress_block(orig_comp, self._zstd_dict, compression_method)
                            
                            # Compare with block file data
                            if orig_plain == block_file_data:
                                console.print(f'   ✅ Block {block_idx}: UNCHANGED - will reuse original ({len(orig_raw):,} bytes)')
                                block_reuse_decisions[block_idx] = (True, orig_raw)
                                reused_count += 1
                            else:
                                # Show detailed comparison for debugging
                                size_match = len(orig_plain) == len(block_file_data)
                                if size_match:
                                    # Find first difference
                                    first_diff = -1
                                    for i in range(len(orig_plain)):
                                        if orig_plain[i] != block_file_data[i]:
                                            first_diff = i
                                            break
                                    console.print(f'   🔧 Block {block_idx}: MODIFIED - will recompress (size OK, first diff at byte {first_diff})')
                                else:
                                    console.print(f'   🔧 Block {block_idx}: MODIFIED - will recompress (size: orig={len(orig_plain):,}, new={len(block_file_data):,})')
                                block_reuse_decisions[block_idx] = (False, None)
                                modified_count += 1
                        
                        except Exception as e:
                            console.print(f'   ⚠️ Block {block_idx}: Reuse check failed, will recompress - {e}')
                            block_reuse_decisions[block_idx] = (False, None)
                            modified_count += 1
                    
                    console.print(f'   📊 Summary: {reused_count} blocks to reuse, {modified_count} blocks to recompress')
                    
                    # Read all block files and assemble (still needed for modified blocks)
                    assembled_data = bytearray()
                    all_blocks_valid = True
                    
                    for block_idx, block_file, expected_size in blocks_info:
                        try:
                            block_data = block_file.read_bytes()
                            if expected_size > 0 and len(block_data) != expected_size:
                                console.print(f'   ⚠️ Block {block_idx} size mismatch: expected {expected_size:,}, got {len(block_data):,}')
                            assembled_data.extend(block_data)
                        except Exception as e:
                            console.print(f'   ❌ Error reading block {block_idx}: {e}')
                            all_blocks_valid = False
                            break
                    
                    if not all_blocks_valid:
                        console.print(f'   ❌ Failed to assemble blocks for {parent_file_path}')
                        continue
                    
                    assembled_bytes = bytes(assembled_data)
                    console.print(f'   ✅ Assembled: {len(assembled_bytes):,} bytes from {len(blocks_info)} blocks')
                    
                    # Check against expected uncompressed size
                    if manifest_info:
                        expected_size = manifest_info.get('uncompressed_size', 0)
                        if expected_size > 0 and len(assembled_bytes) != expected_size:
                            console.print(f'   ⚠️ Size mismatch: assembled {len(assembled_bytes):,} bytes but expected {expected_size:,}')
                    
                    # Now process this assembled file like a regular file
                    mod_name = Path(parent_file_path).name
                    
                    # Create per-file block logger
                    block_logger = BlockLogger(display_name)
                    
                    blocks = parent_entry.compressed_blocks
                    compression_method = parent_entry.compression_method
                    encryption_method = parent_entry.encryption_method if parent_entry.encrypted else 0
                    block_size_val = parent_entry.compression_block_size
                    
                    # Single-block (but assembled from multiple block files)
                    if len(blocks) == 1:
                        block = blocks[0]
                        slot = block.end - block.start
                        
                        comp_method_str = {0: 'NONE', 1: 'ZLIB', 6: 'ZSTD', 8: 'ZSTD_DICT'}.get(compression_method, 'UNKNOWN')
                        enc_method_str = {0: 'NONE', 2: 'AES', 40: 'SM4'}.get(encryption_method, 'UNKNOWN')
                        
                        print(f'   ╔═══════════════════════════════════════════════════════════════════════════════')
                        print(f'   ║ 📄 SINGLE-BLOCK FILE COMPRESSION (FROM BLOCKS)')
                        print(f'   ╠═══════════════════════════════════════════════════════════════════════════════')
                        print(f'   ║ File: {mod_name}')
                        print(f'   ║ Assembled size: {len(assembled_bytes):,} bytes')
                        print(f'   ║ Slot size: {slot:,} bytes')
                        print(f'   ║ Compression: {comp_method_str} (method {compression_method})')
                        print(f'   ║ Encryption: {enc_method_str} (method {encryption_method})')
                        print(f'   ╚═══════════════════════════════════════════════════════════════════════════════')

                        result = None
                        level_used = -1

                        # Try reuse original compressed data
                        try:
                            orig_raw = self._peek_block_content(block, encryption_method)
                            orig_size = len(orig_raw)
                            if parent_entry.encrypted:
                                orig_comp = PakCrypto.decrypt_block(orig_raw, parent_pak_path, encryption_method)
                            else:
                                orig_comp = orig_raw

                            orig_plain = PakCompression.decompress_block(
                                orig_comp, self._zstd_dict, compression_method
                            )

                            if orig_plain == assembled_bytes:
                                result = bytes(orig_raw)
                                reuse_pct = (orig_size / slot) * 100
                                print(f'   🔁 REUSED ORIGINAL: {orig_size:,}/{slot:,} bytes ({reuse_pct:.2f}% slot usage)')
                                block_logger.add_block(0, len(assembled_bytes), orig_size, comp_method_str, -1, True, block.start, block.end)
                        except Exception as e:
                            print(f'   ⚠️ Reuse failed: {e}')

                        # If not reusable, recompress
                        if result is None:
                            best_compressed = None
                            best_size = float('inf')
                            best_level = -1
                            
                            # Determine compression method details
                            if compression_method == const.CM_ZLIB:
                                comp_method_name = "ZLIB"
                                max_level = 9
                                level_step = 1
                            elif compression_method in [const.CM_ZSTD, const.CM_ZSTD_DICT]:
                                comp_method_name = "ZSTD" if compression_method == const.CM_ZSTD else "ZSTD_DICT"
                                max_level = 22
                                level_step = 1
                            else:
                                comp_method_name = "UNKNOWN"
                                max_level = 9
                                level_step = 1
                            
                            print(f'   🔧 Compressing with {comp_method_name} (max level: {max_level}, trying all levels)')
                            print(f'   📏 Original: {len(assembled_bytes):,} bytes, Target slot: {slot:,} bytes')
                            
                            attempts = 0
                            for lvl in range(max_level, 0, -level_step):
                                attempts += 1
                                comp = None

                                try:
                                    if compression_method == const.CM_ZLIB:
                                        actual_level = min(lvl, 9)
                                        comp = zlib.compress(assembled_bytes, level=actual_level)
                                        lvl_display = actual_level
                                    elif compression_method == const.CM_ZSTD:
                                        comp = ZstdCompressor(level=lvl).compress(assembled_bytes)
                                        lvl_display = lvl
                                    elif compression_method == const.CM_ZSTD_DICT and self._zstd_dict is not None:
                                        comp = ZstdCompressor(level=lvl, dict_data=self._zstd_dict).compress(assembled_bytes)
                                        lvl_display = lvl
                                    else:
                                        print(f'   ❌ Unknown compression method: {compression_method}')
                                        break

                                    if comp:
                                        comp_size = len(comp)
                                        ratio = (comp_size / len(assembled_bytes)) * 100
                                        savings = len(assembled_bytes) - comp_size
                                        slot_usage = (comp_size / usable_slot) * 100
                                        
                                        fit_status = "✅ FIT" if comp_size <= slot else "❌ TOO BIG"
                                        
                                        print(f'   │ Attempt {attempts}: Level {lvl_display:>2} │ {len(assembled_bytes):>8,} → {comp_size:>8,} bytes │ Ratio: {ratio:>6.2f}% │ Saved: {savings:>7,} │ Slot: {slot_usage:>6.2f}% │ {fit_status}')
                                        
                                        if comp_size < best_size:
                                            best_size = comp_size
                                            best_compressed = comp
                                            best_level = lvl_display

                                        if comp_size <= usable_slot:
                                            result = comp
                                            level_used = lvl_display
                                            print(f'   └─> ✅ SUCCESS! Compressed {len(assembled_bytes):,} → {comp_size:,} bytes using level {lvl_display} ({slot_usage:.2f}% slot usage)')
                                            break
                                except Exception as e:
                                    print(f'   │ Attempt {attempts}: Level {lvl:>2} │ ⚠️ ERROR: {str(e)}')
                                    continue

                            if result is None:
                                if best_compressed:
                                    overage = best_size - slot
                                    overage_pct = (overage / slot) * 100
                                    print(f'   └─> ❌ FAILED! Best compression: {best_size:,} bytes at level {best_level}')
                                    print(f'       Target slot: {slot:,} bytes')
                                    print(f'       Overage: {overage:,} bytes ({overage_pct:.2f}% over limit)')
                                    print(f'       Tried {attempts} compression levels')
                                logger.log_failure(display_name, 'Compression failed to fit', {'best_size': best_size, 'slot': slot})
                                continue

                            block_logger.add_block(0, len(assembled_bytes), len(result), comp_method_str, level_used, True, block.start, block.end)

                        # Always overwrite the full stored slot range (block-based single-block)
                        if parent_entry.encrypted:
                            if PakCrypto.align_encrypted_content_size(slot, encryption_method) != slot:
                                raise ValueError(f'Block slot size {slot} is not aligned for encryption method {encryption_method}')
                            padded_plain = result + b'\x00' * (slot - len(result))
                            result = PakCrypto.encrypt_block(padded_plain, parent_pak_path, encryption_method)
                            if len(result) != slot:
                                raise ValueError(f'Encrypted block size mismatch: got {len(result)} bytes, expected {slot}')
                            print(f'   🔒 Encrypted with {enc_method_str} (slot-sized): {len(result):,} bytes')
                        else:
                            result = result + b'\x00' * (slot - len(result))

                        work_items.append((parent_pak_path, [(block.start, result)], False))
                        modified_targets.append((parent_pak_path, parent_entry))
                        block_logger.print_summary()
                    
                    # Multi-block (from reassembled data)
                    else:
                        total_slot_size = sum((b.end - b.start for b in blocks))
                        block_size_kb = block_size_val / 1024
                        total_slot_kb = total_slot_size / 1024
                        mod_size_kb = len(assembled_bytes) / 1024
                        
                        comp_method_str = {0: 'NONE', 1: 'ZLIB', 6: 'ZSTD', 8: 'ZSTD_DICT'}.get(compression_method, 'UNKNOWN')
                        enc_method_str = {0: 'NONE', 2: 'AES', 40: 'SM4'}.get(encryption_method, 'UNKNOWN')
                        
                        print(f'   ╔═══════════════════════════════════════════════════════════════════════════════')
                        print(f'   ║ 📦 MULTI-BLOCK FILE COMPRESSION (FROM BLOCKS)')
                        print(f'   ╠═══════════════════════════════════════════════════════════════════════════════')
                        print(f'   ║ File: {mod_name}')
                        print(f'   ║ Assembled size: {len(assembled_bytes):,} bytes ({mod_size_kb:.2f} KB)')
                        print(f'   ║ Blocks: {len(blocks)} blocks × {block_size_val:,} bytes ({block_size_kb:.2f} KB per block)')
                        print(f'   ║ Total slot space: {total_slot_size:,} bytes ({total_slot_kb:.2f} KB)')
                        print(f'   ║ Compression: {comp_method_str} (method {compression_method})')
                        print(f'   ║ Encryption: {enc_method_str} (method {encryption_method})')
                        print(f'   ╚═══════════════════════════════════════════════════════════════════════════════')

                        chunks = list(it.batched(assembled_bytes, block_size_val))
                        chunks = [bytes(chunk) if isinstance(chunk, tuple) else chunk for chunk in chunks]
                        if len(chunks) > len(blocks):
                            print(f'   ❌ Too many chunks: {len(chunks)} > {len(blocks)} blocks')
                            logger.log_failure(display_name, 'Too many chunks', {'chunks': len(chunks), 'blocks': len(blocks)})
                            continue

                        compressed_chunks = []
                        all_fit = True
                        
                        # Build a map of which actual block indices we have
                        actual_block_indices = sorted(block_reuse_decisions.keys())
                        
                        # Process ALL blocks (0 to len(blocks)-1), not just chunks
                        for actual_block_idx in range(len(blocks)):
                            # actual_block_idx here is the logical block index (block_N). Map to stored index.
                            stored_idx = block_indices[actual_block_idx] if actual_block_idx < len(block_indices) else actual_block_idx
                            block = blocks[stored_idx]
                            slot = block.end - block.start
                            
                            # Check if we have this block in our reuse decisions
                            if actual_block_idx in block_reuse_decisions:
                                should_reuse, orig_compressed = block_reuse_decisions[actual_block_idx]
                                
                                if should_reuse and orig_compressed:
                                    # Reuse original
                                    result = bytes(orig_compressed)
                                    print(f'      🔄 Block {actual_block_idx}: ♻️  REUSED original ({len(result):,} bytes)')
                                    block_logger.add_block(actual_block_idx, block_size_val if actual_block_idx < len(chunks) else 0, len(result), comp_method_str + " (REUSED)", -1, True, block.start, block.end)
                                    compressed_chunks.append((block.start, result))
                                    continue
                                else:
                                    # Block was modified - get the chunk data
                                    # Find this block in chunks list
                                    chunk_idx = actual_block_indices.index(actual_block_idx) if actual_block_idx in actual_block_indices else -1
                                    if chunk_idx < 0 or chunk_idx >= len(chunks):
                                        print(f'      ⚠️ Block {actual_block_idx}: Data not found in chunks')
                                        all_fit = False
                                        break
                                    
                                    chunk = chunks[chunk_idx]
                                    orig_chunk_size = len(chunk)
                                    print(f'      🔄 Block {actual_block_idx}: {orig_chunk_size:,} bytes → Slot: {slot:,} bytes (must fit)')
                                    print(f'         🔁 Block modified, recompressing...')
                            else:
                                # Block not in edited folder - must reuse original
                                try:
                                    orig_raw = self._peek_block_content(block, encryption_method)
                                    result = bytes(orig_raw)
                                    print(f'      🔄 Block {actual_block_idx}: ♻️  AUTO-REUSED (not in edited folder, {len(result):,} bytes)')
                                    block_logger.add_block(actual_block_idx, block_size_val, len(result), comp_method_str + " (AUTO-REUSED)", -1, True, block.start, block.end)
                                    compressed_chunks.append((block.start, result))
                                    continue
                                except Exception as e:
                                    print(f'      ❌ Block {actual_block_idx}: Failed to reuse original - {e}')
                                    all_fit = False
                                    break

                            result = None
                            level_used = -1

                            # Recompress this chunk
                            best_compressed = None
                            best_size = float('inf')
                            best_level = -1
                            
                            if compression_method == const.CM_ZLIB:
                                comp_method_name = "ZLIB"
                                max_level = 9
                                level_step = 1
                            elif compression_method in [const.CM_ZSTD, const.CM_ZSTD_DICT]:
                                comp_method_name = "ZSTD" if compression_method == const.CM_ZSTD else "ZSTD_DICT"
                                max_level = 22
                                level_step = 1
                            else:
                                comp_method_name = "UNKNOWN"
                                max_level = 9
                                level_step = 1
                            
                            print(f'         🔧 Compressing with {comp_method_name} (trying levels 22→1)')
                            
                            attempts = 0
                            for lvl in range(max_level, 0, -level_step):
                                attempts += 1
                                comp = None

                                try:
                                    if compression_method == const.CM_ZLIB:
                                        actual_level = min(lvl, 9)
                                        comp = zlib.compress(chunk, level=actual_level)
                                        lvl_display = actual_level
                                    elif compression_method == const.CM_ZSTD:
                                        comp = ZstdCompressor(level=lvl).compress(chunk)
                                        lvl_display = lvl
                                    elif compression_method == const.CM_ZSTD_DICT and self._zstd_dict is not None:
                                        comp = ZstdCompressor(level=lvl, dict_data=self._zstd_dict).compress(chunk)
                                        lvl_display = lvl
                                    else:
                                        break

                                    if comp:
                                        comp_size = len(comp)
                                        slot_remaining = usable_slot - comp_size
                                        slot_usage = (comp_size / usable_slot) * 100
                                        
                                        fit_status = "✅" if comp_size <= usable_slot else "❌"
                                        
                                        print(f'         │ L{lvl_display:>2} │ {orig_chunk_size:>8,} → {comp_size:>8,} │ Slot: {usable_slot:>8,} ({slot_usage:>6.2f}%) │ Free: {slot_remaining:>7,} │ {fit_status}')
                                        
                                        if comp_size < best_size:
                                            best_size = comp_size
                                            best_compressed = comp
                                            best_level = lvl_display
                                        
                                        if comp_size <= usable_slot:
                                            result = comp
                                            level_used = lvl_display
                                            print(f'         └─> ✅ SUCCESS at Level {lvl_display}!')
                                            break
                                except Exception as e:
                                    print(f'         │ L{lvl:>2} │ ⚠️ ERROR: {str(e)}')
                                    continue

                            if result is None:
                                all_fit = False
                                if best_compressed:
                                    overage = best_size - slot
                                    overage_pct = (overage / slot) * 100
                                    print(f'         └─> ❌ FAILED! Best: L{best_level} = {best_size:,} bytes (over by {overage:,} bytes / {overage_pct:.2f}%)')
                                else:
                                    print(f'         └─> ❌ FAILED! No valid compression found')
                                block_logger.add_block(actual_block_idx, orig_chunk_size, best_size if best_compressed else orig_chunk_size, comp_method_str, best_level, False, block.start, block.end)
                                break

                            # Always overwrite the full stored slot range.
                            if parent_entry.encrypted:
                                if PakCrypto.align_encrypted_content_size(slot, encryption_method) != slot:
                                    raise ValueError(f'Block slot size {slot} is not aligned for encryption method {encryption_method}')
                                padded_plain = result + b'\x00' * (slot - len(result))
                                result = PakCrypto.encrypt_block(padded_plain, parent_pak_path, encryption_method)
                                if len(result) != slot:
                                    raise ValueError(f'Encrypted block size mismatch: got {len(result)} bytes, expected {slot}')
                            else:
                                result = result + b'\x00' * (slot - len(result))

                            block_logger.add_block(actual_block_idx, orig_chunk_size, len(result), comp_method_str, level_used, True, block.start, block.end)
                            compressed_chunks.append((block.start, result))

                        if all_fit:
                            work_items.append((parent_pak_path, compressed_chunks, True))
                            modified_targets.append((parent_pak_path, parent_entry))
                            # For successful repacks, utilization is 100%
                            logger.log_success(display_name, total_slot_size, total_slot_size)
                            block_logger.print_summary()
                        else:
                            print('   ❌ Some blocks failed to fit')
                            logger.log_failure(display_name, 'Block compression failed', {'total_slot': total_slot_size})

            if not work_items:
                print('\n⚠️ Nothing to repack')
                temp_pak.unlink(missing_ok=True)
            else:
                print(f'\n📝 Writing {len(work_items)} files...')

                try:
                    with open(temp_pak, 'r+b') as fp:
                        for entry_path, block_data, is_multi in work_items:
                            try:
                                for offset, data in block_data:
                                    fp.seek(offset)
                                    fp.write(data)

                                print(f'✅ {Path(entry_path).name}: {len(block_data)} block(s) written')
                            except Exception as e:
                                print(f'❌ Write error for {Path(entry_path).name}: {e}')

                    temp_pak.replace(output_pak)
                    print(f'\n✅ Repack Complete! Saved to: {output_pak}')

                    # -------------------- Integrity verification --------------------
                    # Re-open the repacked PAK and attempt to decrypt+decompress all modified entries.
                    # This catches common corruption causes (wrong block order, padding, size issues).
                    try:
                        with open(output_pak, 'rb') as vf:
                            vbuf = memoryview(vf.read())

                        ok = 0
                        bad = 0
                        for vpath, ventry in modified_targets:
                            try:
                                enc_m = ventry.encryption_method
                                comp_m = ventry.compression_method

                                if ventry.encrypted and enc_m == 17:
                                    raise ValueError('EM_UNKNOWN_17 not supported')

                                # Uncompressed
                                if comp_m == const.CM_NONE:
                                    sz = PakCrypto.align_encrypted_content_size(ventry.size, enc_m)
                                    data = vbuf[ventry.offset:][:sz]
                                    if ventry.encrypted:
                                        data = PakCrypto.decrypt_block(bytes(data), vpath, enc_m)
                                    plain = bytes(data)
                                else:
                                    parts = []
                                    for bi in PakCrypto.generate_block_indices(len(ventry.compressed_blocks), enc_m):
                                        b = ventry.compressed_blocks[bi]
                                        bsz = PakCrypto.align_encrypted_content_size(b.end - b.start, enc_m)
                                        blk = vbuf[b.start:][:bsz]
                                        blk_bytes = bytes(blk)
                                        if ventry.encrypted:
                                            blk_bytes = PakCrypto.decrypt_block(blk_bytes, vpath, enc_m)
                                        dec = PakCompression.decompress_block(blk_bytes, self._zstd_dict, comp_m)
                                        parts.append(dec)
                                    plain = b''.join(parts)

                                # Trim to declared uncompressed size for validation
                                if ventry.uncompressed_size and len(plain) >= ventry.uncompressed_size:
                                    plain = plain[:ventry.uncompressed_size]

                                if ventry.uncompressed_size and len(plain) != ventry.uncompressed_size:
                                    raise ValueError(f'Uncompressed size mismatch: got {len(plain)}, expected {ventry.uncompressed_size}')

                                ok += 1
                            except Exception as ve:
                                bad += 1
                                print(f'❌ Verify failed: {vpath} -> {ve}')

                        if bad == 0:
                            print(f'✅ Verification passed for {ok} modified entr(y/ies).')
                        else:
                            print(f'⚠️ Verification: {ok} passed, {bad} failed. The output PAK may be broken.')
                    except Exception as ve:
                        print(f'⚠️ Verification step failed to run: {ve}')
                    # ----------------------------------------------------------------

                    logger.print_summary()
                except Exception as e:
                    print(f'❌ File Error: {e}')                

# ==================== MAIN EXECUTION ====================
ANA_DIZIN = Path(__file__).resolve().parent
PAKS_DIR = ANA_DIZIN / 'PAKS'
UNPACKED_DIR = ANA_DIZIN / 'unpacked'
REPACKED_DIR = ANA_DIZIN / 'repacked_obb'
EXTRACTED_DIR = ANA_DIZIN / 'extracted'

def _ensure_base_dirs():
    ANA_DIZIN.mkdir(parents=True, exist_ok=True)
    PAKS_DIR.mkdir(exist_ok=True)
    UNPACKED_DIR.mkdir(exist_ok=True)
    REPACKED_DIR.mkdir(exist_ok=True)
    EXTRACTED_DIR.mkdir(exist_ok=True)
    console.print(f'[+] Directories initialized at: {ANA_DIZIN}')

def main():
    _ensure_base_dirs()
    
    while True:
        console.print('\n🎮 PAK File Manager - Enhanced with Manifest')
        console.print('══════════════════════════════════════════')
        console.print('1. 🚀 Unpack PAK with Detailed Manifest')
        console.print('2. 🔄 Repack Using Manifest (Safe)')
        console.print('3. 📄 Selective Extract with Manifest')
        console.print('4. 📊 View Manifest Information')
        console.print('5. ❓ Help - How to Use This Tool')
        console.print('6. ❌ Exit')
        
        try:
            choice = input('\nSelection (1-6): ').strip()
        except (KeyboardInterrupt, EOFError):
            break
        
        if choice == '1':
            # Unpack with manifest
            paks = sorted([p for p in PAKS_DIR.glob('*.pak') if p.is_file()])
            if not paks:
                console.print('❌ No .pak files found in PAKS/')
                continue
            
            console.print('\n=== UNPACK WITH MANIFEST ===')
            console.print('1. Unpack All Paks')
            console.print('2. Select Single Pak')
            console.print('3. Back')
            alt = input('Selection: ').strip()
            
            # Ask for extraction mode
            console.print('Choose extraction mode:')
            console.print('1. Full file extraction (normal)')
            console.print('2. Block-based extraction (split into .block_N files)')
            mode_choice = input('Mode (1/2): ').strip()
            use_blocks = (mode_choice == '2')
            
            if alt == '1':
                for pak in paks:
                    try:
                        console.print(f'\nProcessing: {pak.name}')
                        pak_obj = TencentPakFile(pak)
                        out_dir = UNPACKED_DIR / pak.stem
                        pak_obj.dump(out_dir, use_block_splitting=use_blocks)
                    except Exception as e:
                        console.print(f'❌ Failed: {e}')
                        traceback.print_exc()
            elif alt == '2':
                for i, pak in enumerate(paks, 1):
                    console.print(f'{i}. {pak.name}')
                try:
                    idx = int(input('Select: ')) - 1
                    if 0 <= idx < len(paks):
                        pak_obj = TencentPakFile(paks[idx])
                        out_dir = UNPACKED_DIR / paks[idx].stem
                        pak_obj.dump(out_dir, use_block_splitting=use_blocks)
                except (ValueError, IndexError):
                    console.print('❌ Invalid selection')
        
        elif choice == '2':
            # Repack using manifest
            unpacked_folders = sorted([p for p in UNPACKED_DIR.iterdir() if p.is_dir()])
            if not unpacked_folders:
                console.print('❌ No unpacked folders found. Unpack first.')
                continue
            
            # Find folders with both manifest and original pak
            valid_folders = []
            for folder in unpacked_folders:
                manifest = folder / 'manifest.json'
                original_pak = PAKS_DIR / f"{folder.name}.pak"
                if manifest.exists() and original_pak.exists():
                    valid_folders.append(folder)
            
            if not valid_folders:
                console.print('❌ No valid folders with manifest and original PAK')
                continue
            
            console.print('\n=== REPACK USING MANIFEST ===')
            for i, folder in enumerate(valid_folders, 1):
                console.print(f'{i}. {folder.name}')
            
            try:
                idx = int(input('Select folder to repack: ')) - 1
            except ValueError:
                console.print('❌ Invalid selection')
                continue

            if 0 <= idx < len(valid_folders):
                folder = valid_folders[idx]
                edited_folder = folder / 'edited'

                if not edited_folder.exists():
                    console.print('❌ No "edited" folder found. Place your mods there first.')
                    continue

                # Check for edited files
                edited_files = list(edited_folder.rglob('*'))
                if not edited_files:
                    console.print('⚠️ No files in "edited" folder')
                    continue

                output_pak = REPACKED_DIR / f'{folder.name}.pak'

                console.print(Panel(
                    f"[cyan]Repack Configuration[/cyan]\n"
                    f"• Source: {edited_folder}\n"
                    f"• Original: {PAKS_DIR / folder.name}\n"
                    f"• Output: {output_pak}\n"
                    f"• Files to process: {len(edited_files)}",
                    title="Repack Setup"
                ))

                confirm = input('Proceed? (y/N): ').strip().lower()
                if confirm == 'y':
                    try:
                        pak_obj = TencentPakFile(PAKS_DIR / f"{folder.name}.pak")
                        pak_obj.repack(edited_folder, output_pak)
                    except Exception as e:
                        console.print(f'❌ Repack failed: {e}')
                        traceback.print_exc()
            else:
                console.print('❌ Invalid selection')
        
        elif choice == '3':
            # Selective extract - simplified version
            paks = sorted([p for p in PAKS_DIR.glob('*.pak') if p.is_file()])
            if not paks:
                console.print('❌ No .pak files found')
                continue
            
            console.print('\n=== SELECTIVE EXTRACT ===')
            for i, pak in enumerate(paks, 1):
                console.print(f'{i}. {pak.name}')
            
            try:
                idx = int(input('Select PAK: ')) - 1
                if 0 <= idx < len(paks):
                    pak_obj = TencentPakFile(paks[idx])
                    
                    # Simple extraction to extracted folder
                    output_dir = EXTRACTED_DIR / paks[idx].stem
                    output_dir.mkdir(parents=True, exist_ok=True)
                    
                    console.print(f"[green]Extracting to: {output_dir}")
                    
                    # Just extract all files
                    for dir_path, dir_dict in pak_obj._index.items():
                        for file_name, entry in dir_dict.items():
                            if entry.encrypted and entry.encryption_method == 17:
                                continue
                            
                            file_dir = output_dir / dir_path
                            file_dir.mkdir(parents=True, exist_ok=True)
                            file_path = file_dir / file_name
                            
                            try:
                                pak_obj._write_to_disk(file_path, entry)
                                console.print(f"  [green]✓ {file_name}")
                            except Exception as e:
                                console.print(f"  [red]✗ {file_name}: {e}")
                    
                    console.print(f"[green]✅ Extraction complete!")
            except (ValueError, IndexError):
                console.print('❌ Invalid selection')
        
        elif choice == '4':
            # View manifest info
            manifests = list(UNPACKED_DIR.rglob('manifest.json'))
            if not manifests:
                console.print('❌ No manifests found. Unpack a PAK first.')
                continue
            
            console.print('\n=== MANIFEST VIEWER ===')
            for i, manifest in enumerate(manifests, 1):
                console.print(f'{i}. {manifest.parent.name}')
            
            try:
                idx = int(input('Select manifest: ')) - 1
                if 0 <= idx < len(manifests):
                    with open(manifests[idx], 'r') as f:
                        manifest_data = json.load(f)
                    
                    console.print(Panel(
                        f"[bold cyan]Manifest Overview[/bold cyan]\n"
                        f"• PAK: {manifest_data.get('pak_file', 'Unknown')}\n"
                        f"• Created: {manifest_data.get('created_at', 'Unknown')}\n"
                        f"• Version: {manifest_data.get('version', '1.0')}\n"
                        f"• Total Files: {manifest_data.get('total_files', 0)}\n"
                        f"• Total Blocks: {manifest_data.get('total_blocks', 0)}",
                        title="Manifest Summary"
                    ))
                    
                    # Show compression distribution
                    comp_stats = manifest_data.get('compression_stats', {})
                    if comp_stats:
                        table = Table(title="Compression Distribution", show_header=True)
                        table.add_column("Method", style="cyan")
                        table.add_column("Count", justify="right")
                        table.add_column("Percentage", justify="right")
                        
                        total = sum(comp_stats.values())
                        for method, count in comp_stats.items():
                            percent = (count / total) * 100
                            table.add_row(method, str(count), f"{percent:.1f}%")
                        
                        console.print(table)
                    
                    # List files
                    list_files = input('\nList all files? (y/N): ').lower()
                    if list_files == 'y':
                        files = manifest_data.get('files', {})
                        for i, (path, info) in enumerate(files.items(), 1):
                            if i > 50:
                                console.print(f'... and {len(files) - 50} more')
                                break
                            console.print(f'{i}. {Path(path).name} ({info.get("compression_method_name", "N/A")}, {info.get("num_blocks", 0)} blocks)')
            except (ValueError, IndexError):
                console.print('❌ Invalid selection')
        
        elif choice == '5':
            # Help documentation
            console.print('\n' + '='*80)
            console.print('📖 PAK FILE MANAGER - COMPLETE GUIDE')
            console.print('='*80)
            
            console.print('\n🎯 OVERVIEW')
            console.print('-' * 80)
            console.print('This tool unpacks, modifies, and repacks PUBG Mobile PAK files.')
            console.print('It uses a manifest system to track file structure and compression.')
            
            console.print('\n📁 FOLDER STRUCTURE')
            console.print('-' * 80)
            console.print('PAKS/          → Place your original .pak files here')
            console.print('unpacked/      → Extracted files and manifests')
            console.print('  └─ pakname/')
            console.print('     ├─ manifest.json    (auto-generated, tracks file info)')
            console.print('     ├─ edited/          (PUT YOUR MODIFIED FILES HERE)')
            console.print('     └─ [extracted files]')
            console.print('repacked_pak/  → Your repacked .pak files')
            
            console.print('\n📋 STEP-BY-STEP WORKFLOW')
            console.print('-' * 80)
            console.print('1️⃣  UNPACK (Option 1):')
            console.print('   • Place .pak files in PAKS/ folder')
            console.print('   • Run Option 1 and select your PAK')
            console.print('   • Choose extraction mode:')
            console.print('     - Normal: Full files (easy to view/edit)')
            console.print('     - Block: Split into chunks (for very large files)')
            console.print('   • Files extract to: unpacked/pakname/')
            console.print('   • "edited" folder is created automatically')
            
            console.print('\n2️⃣  MODIFY:')
            console.print('   • Find the file you want to edit in unpacked/pakname/')
            console.print('   • Edit it with appropriate tools (UAssetGUI, hex editor, etc.)')
            console.print('   • COPY the modified file to: unpacked/pakname/edited/')
            console.print('   • ⚠️ IMPORTANT: Keep the SAME folder structure!')
            console.print('     Example:')
            console.print('       Original: unpacked/mini_obb/ShadowTrackerExtra/Content/Item.uasset')
            console.print('       Modified: unpacked/mini_obb/edited/ShadowTrackerExtra/Content/Item.uasset')
            
            console.print('\n3️⃣  REPACK (Option 2):')
            console.print('   • Run Option 2 and select the folder')
            console.print('   • Tool reads manifest.json to know how to compress')
            console.print('   • Only files in "edited" folder are repacked')
            console.print('   • Output: repacked_pak/pakname.pak')
            
            console.print('\n⚠️  COMMON ISSUES & SOLUTIONS')
            console.print('-' * 80)
            console.print('❌ "File too large" error:')
            console.print('   → Your modified file is bigger than the original')
            console.print('   → Try reducing file size or use smaller modifications')
            
            console.print('\n❌ "No matching PAK entry":')
            console.print('   → Folder structure doesn\'t match')
            console.print('   → Check the path matches the original exactly')
            
            console.print('\n❌ "Manifest not found":')
            console.print('   → Unpack first using Option 1')
            console.print('   → Make sure manifest.json exists in unpacked/pakname/')
            
            console.print('\n🔧 COMPRESSION INFO')
            console.print('-' * 80)
            console.print('• Files are compressed with ZSTD (levels 1-22)')
            console.print('• Tool tries all compression levels to fit your file')
            console.print('• Encrypted files use SM4 encryption')
            console.print('• Block size: 64KB per block')
            
            console.print('\n💡 PRO TIPS')
            console.print('-' * 80)
            console.print('✓ Always keep backups of original PAK files')
            console.print('✓ Don\'t modify the manifest.json manually')
            console.print('✓ Test repacked files on a backup device first')
            console.print('✓ Keep modifications small to avoid compression issues')
            console.print('✓ Use "View Manifest" (Option 4) to check file info')
            
            console.print('\n📊 OTHER OPTIONS')
            console.print('-' * 80)
            console.print('Option 3 (Selective Extract):')
            console.print('  → Extract only specific files by pattern')
            console.print('Option 4 (View Manifest):')
            console.print('  → See compression info, block count, file sizes')
            
            console.print('\n' + '='*80)
            input('\n Press Enter to return to menu...')
        
        elif choice == '6':
            console.print('👋 Goodbye!')
            break
        
        else:
            console.print('❌ Invalid selection')

if __name__ == '__main__':
    main()