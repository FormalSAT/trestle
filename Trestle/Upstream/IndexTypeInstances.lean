/- Copyright (c) 2024 James Gallicchio.

Authors: James Gallicchio
-/

import Trestle.Upstream.IndexType

namespace Trestle

deriving instance IndexType for Bool
deriving instance IndexType for BitVec
deriving instance IndexType for UInt8
deriving instance IndexType for UInt16
deriving instance IndexType for UInt32
deriving instance IndexType for UInt64
