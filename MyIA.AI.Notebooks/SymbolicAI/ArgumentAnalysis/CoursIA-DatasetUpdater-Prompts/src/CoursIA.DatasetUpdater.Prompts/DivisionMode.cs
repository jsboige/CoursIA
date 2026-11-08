// Ported from Argumentum/Argumentum, file Generation/Converters/Argumentum.AssetConverter/DatasetUpdater/DivisionMode.cs
// Original commit: ac33f607a4889d8a982093c413804ed25bef3dc0 (EPIC #4960 tranche C, 2026-07-03)
// Original author: jsboige
// Upstream license: LGPL-3.0 OR AGPL-3.0 (network use). See NOTICE in this directory.
//
// This file is free software; you can redistribute it and/or modify it under the
// terms of the GNU Lesser General Public License as published by the Free Software
// Foundation; either version 3 of the License, or (at your option) any later
// version. See <https://www.gnu.org/licenses/lgpl-3.0.html>.
//
// Modifications from upstream: namespace moved from `Argumentum.AssetConverter`
// to `CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater` (LGPL
// v3 §5 modification log). No other changes — the enum surface is preserved
// verbatim, byte-for-byte.

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater;

public enum DivisionMode
{
	SequentialChunks,
	PKHierarchicalChar
}