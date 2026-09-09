import DR.Rectangular.FourRowFiniteLinear

/-! Generated sparse exact equations; physical coverage is a separate theorem. -/

set_option maxRecDepth 100000

namespace DittertRybin

private def fourRowFiniteCoefficientRowDataChunk0 : Array (FourRowFiniteCoefficientRow) :=
  #[⟨[(⟨0, by decide⟩, 1)], 1, 0⟩,
    ⟨[(⟨1, by decide⟩, 2), (⟨17, by decide⟩, 1)], 5, 0⟩,
    ⟨[(⟨2, by decide⟩, 2), (⟨48, by decide⟩, 1)], 5, 0⟩,
    ⟨[(⟨3, by decide⟩, 2), (⟨79, by decide⟩, 1)], 5, 0⟩,
    ⟨[(⟨4, by decide⟩, 1), (⟨18, by decide⟩, 2), (⟨23, by decide⟩, 1)], 10, 0⟩,
    ⟨[(⟨5, by decide⟩, 2), (⟨19, by decide⟩, 4), (⟨137, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨6, by decide⟩, 2), (⟨20, by decide⟩, 2), (⟨49, by decide⟩, 2), (⟨158, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨7, by decide⟩, 2), (⟨21, by decide⟩, 2), (⟨80, by decide⟩, 2), (⟨167, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨8, by decide⟩, 2), (⟨22, by decide⟩, 2), (⟨81, by decide⟩, 2), (⟨216, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨9, by decide⟩, 1), (⟨50, by decide⟩, 2), (⟨62, by decide⟩, 1)], 10, 0⟩,
    ⟨[(⟨10, by decide⟩, 2), (⟨51, by decide⟩, 2), (⟨82, by decide⟩, 2), (⟨185, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨11, by decide⟩, 2), (⟨52, by decide⟩, 4), (⟨281, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨12, by decide⟩, 2), (⟨53, by decide⟩, 2), (⟨85, by decide⟩, 2), (⟨298, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨13, by decide⟩, 1), (⟨83, by decide⟩, 2), (⟨112, by decide⟩, 1)], 10, 0⟩,
    ⟨[(⟨14, by decide⟩, 2), (⟨84, by decide⟩, 4), (⟨254, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨15, by decide⟩, 2), (⟨86, by decide⟩, 4), (⟨338, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨16, by decide⟩, 2), (⟨87, by decide⟩, 4), (⟨356, by decide⟩, 1)], 20, 0⟩,
    ⟨[(⟨24, by decide⟩, 4), (⟨28, by decide⟩, 2), (⟨138, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨25, by decide⟩, 2), (⟨26, by decide⟩, 2), (⟨54, by decide⟩, 1), (⟨88, by decide⟩, 1), (⟨159, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨27, by decide⟩, 4), (⟨96, by decide⟩, 2), (⟨217, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨29, by decide⟩, 6), (⟨139, by decide⟩, 6), (⟨143, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨30, by decide⟩, 4), (⟨55, by decide⟩, 2), (⟨140, by decide⟩, 2), (⟨160, by decide⟩, 4), (⟨228, by decide⟩, 1)], 60, 0⟩,
    ⟨[(⟨31, by decide⟩, 2), (⟨32, by decide⟩, 2), (⟨89, by decide⟩, 2), (⟨141, by decide⟩, 2), (⟨168, by decide⟩, 2), (⟨175, by decide⟩, 1), (⟨218, by decide⟩, 2)], 60, 0⟩,
    ⟨[(⟨33, by decide⟩, 4), (⟨97, by decide⟩, 2), (⟨142, by decide⟩, 2), (⟨219, by decide⟩, 4), (⟨236, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨34, by decide⟩, 1), (⟨56, by decide⟩, 2), (⟨63, by decide⟩, 2), (⟨106, by decide⟩, 1), (⟨161, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨35, by decide⟩, 2), (⟨57, by decide⟩, 2), (⟨90, by decide⟩, 2), (⟨162, by decide⟩, 2), (⟨170, by decide⟩, 2), (⟨186, by decide⟩, 2), (⟨191, by decide⟩, 1)], 60, 0⟩,
    ⟨[(⟨36, by decide⟩, 2), (⟨58, by decide⟩, 2), (⟨98, by decide⟩, 2), (⟨163, by decide⟩, 2), (⟨187, by decide⟩, 2), (⟨220, by decide⟩, 2), (⟨246, by decide⟩, 1)], 60, 0⟩,
    ⟨[(⟨37, by decide⟩, 2), (⟨59, by decide⟩, 4), (⟨164, by decide⟩, 4), (⟨282, by decide⟩, 2), (⟨332, by decide⟩, 1)], 60, 0⟩,
    ⟨[(⟨38, by decide⟩, 2), (⟨60, by decide⟩, 2), (⟨93, by decide⟩, 2), (⟨165, by decide⟩, 2), (⟨173, by decide⟩, 2), (⟨299, by decide⟩, 2), (⟨310, by decide⟩, 1)], 60, 0⟩,
    ⟨[(⟨39, by decide⟩, 2), (⟨61, by decide⟩, 2), (⟨102, by decide⟩, 2), (⟨166, by decide⟩, 2), (⟨224, by decide⟩, 2), (⟨300, by decide⟩, 2), (⟨366, by decide⟩, 1)], 60, 0⟩,
    ⟨[(⟨40, by decide⟩, 1), (⟨66, by decide⟩, 1), (⟨91, by decide⟩, 2), (⟨107, by decide⟩, 2), (⟨169, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨41, by decide⟩, 2), (⟨92, by decide⟩, 2), (⟨100, by decide⟩, 2), (⟨171, by decide⟩, 2), (⟨196, by decide⟩, 1), (⟨221, by decide⟩, 2), (⟨248, by decide⟩, 2)], 60, 0⟩]

private def fourRowFiniteCoefficientRowDataChunk1 : Array (FourRowFiniteCoefficientRow) :=
  #[⟨[(⟨42, by decide⟩, 2), (⟨94, by decide⟩, 4), (⟨172, by decide⟩, 4), (⟨287, by decide⟩, 1), (⟨333, by decide⟩, 2)], 60, 0⟩,
    ⟨[(⟨43, by decide⟩, 2), (⟨95, by decide⟩, 2), (⟨104, by decide⟩, 2), (⟨174, by decide⟩, 2), (⟨225, by decide⟩, 2), (⟨320, by decide⟩, 1), (⟨357, by decide⟩, 2)], 60, 0⟩,
    ⟨[(⟨44, by decide⟩, 1), (⟨99, by decide⟩, 2), (⟨113, by decide⟩, 2), (⟨117, by decide⟩, 1), (⟨222, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨45, by decide⟩, 2), (⟨101, by decide⟩, 4), (⟨223, by decide⟩, 4), (⟨255, by decide⟩, 2), (⟨259, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨46, by decide⟩, 2), (⟨103, by decide⟩, 4), (⟨226, by decide⟩, 4), (⟨339, by decide⟩, 2), (⟨343, by decide⟩, 1)], 60, 0⟩,
    ⟨[(⟨47, by decide⟩, 2), (⟨105, by decide⟩, 4), (⟨227, by decide⟩, 4), (⟨358, by decide⟩, 2), (⟨378, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨64, by decide⟩, 4), (⟨71, by decide⟩, 2), (⟨283, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨65, by decide⟩, 4), (⟨123, by decide⟩, 2), (⟨301, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨67, by decide⟩, 2), (⟨108, by decide⟩, 4), (⟨148, by decide⟩, 1), (⟨177, by decide⟩, 4), (⟨231, by decide⟩, 2)], 60, 0⟩,
    ⟨[(⟨68, by decide⟩, 2), (⟨72, by decide⟩, 2), (⟨109, by decide⟩, 2), (⟨188, by decide⟩, 2), (⟨202, by decide⟩, 1), (⟨284, by decide⟩, 2), (⟨304, by decide⟩, 2)], 60, 0⟩,
    ⟨[(⟨69, by decide⟩, 2), (⟨110, by decide⟩, 2), (⟨124, by decide⟩, 2), (⟨189, by decide⟩, 2), (⟨208, by decide⟩, 1), (⟨302, by decide⟩, 2), (⟨315, by decide⟩, 2)], 60, 0⟩,
    ⟨[(⟨70, by decide⟩, 2), (⟨111, by decide⟩, 2), (⟨125, by decide⟩, 2), (⟨190, by decide⟩, 2), (⟨265, by decide⟩, 1), (⟨303, by decide⟩, 2), (⟨359, by decide⟩, 2)], 60, 0⟩,
    ⟨[(⟨73, by decide⟩, 6), (⟨285, by decide⟩, 6), (⟨294, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨74, by decide⟩, 4), (⟨126, by decide⟩, 2), (⟨286, by decide⟩, 2), (⟨307, by decide⟩, 4), (⟨349, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨75, by decide⟩, 1), (⟨114, by decide⟩, 2), (⟨115, by decide⟩, 2), (⟨129, by decide⟩, 1), (⟨305, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨76, by decide⟩, 2), (⟨119, by decide⟩, 4), (⟨257, by decide⟩, 2), (⟨273, by decide⟩, 1), (⟨306, by decide⟩, 4)], 60, 0⟩,
    ⟨[(⟨77, by decide⟩, 2), (⟨127, by decide⟩, 4), (⟨308, by decide⟩, 4), (⟨341, by decide⟩, 2), (⟨352, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨78, by decide⟩, 2), (⟨128, by decide⟩, 4), (⟨309, by decide⟩, 4), (⟨363, by decide⟩, 2), (⟨386, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨116, by decide⟩, 4), (⟨133, by decide⟩, 2), (⟨360, by decide⟩, 2)], 30, 0⟩,
    ⟨[(⟨118, by decide⟩, 6), (⟨154, by decide⟩, 1), (⟨239, by decide⟩, 6)], 60, 24⟩,
    ⟨[(⟨120, by decide⟩, 2), (⟨121, by decide⟩, 2), (⟨130, by decide⟩, 2), (⟨212, by decide⟩, 1), (⟨256, by decide⟩, 2), (⟨325, by decide⟩, 2), (⟨361, by decide⟩, 2)], 60, 0⟩,
    ⟨[(⟨122, by decide⟩, 4), (⟨134, by decide⟩, 2), (⟨258, by decide⟩, 2), (⟨277, by decide⟩, 1), (⟨362, by decide⟩, 4)], 60, 24⟩,
    ⟨[(⟨131, by decide⟩, 6), (⟨296, by decide⟩, 1), (⟨340, by decide⟩, 6)], 60, 24⟩,
    ⟨[(⟨132, by decide⟩, 4), (⟨135, by decide⟩, 2), (⟨342, by decide⟩, 2), (⟨354, by decide⟩, 1), (⟨364, by decide⟩, 4)], 60, 24⟩,
    ⟨[(⟨136, by decide⟩, 6), (⟨365, by decide⟩, 6), (⟨389, by decide⟩, 1)], 60, 24⟩,
    ⟨[(⟨144, by decide⟩, 20)], 120, 120⟩,
    ⟨[(⟨145, by decide⟩, 6), (⟨146, by decide⟩, 2), (⟨176, by decide⟩, 6), (⟨229, by decide⟩, 6)], 120, 48⟩,
    ⟨[(⟨147, by decide⟩, 8), (⟨237, by decide⟩, 12)], 120, 120⟩,
    ⟨[(⟨149, by decide⟩, 2), (⟨178, by decide⟩, 4), (⟨179, by decide⟩, 4), (⟨192, by decide⟩, 4), (⟨230, by decide⟩, 4), (⟨247, by decide⟩, 2)], 120, 0⟩,
    ⟨[(⟨150, by decide⟩, 2), (⟨180, by decide⟩, 4), (⟨197, by decide⟩, 2), (⟨232, by decide⟩, 2), (⟨238, by decide⟩, 4), (⟨240, by decide⟩, 2), (⟨249, by decide⟩, 4)], 120, 48⟩,
    ⟨[(⟨151, by decide⟩, 2), (⟨181, by decide⟩, 8), (⟨234, by decide⟩, 4), (⟨288, by decide⟩, 2), (⟨334, by decide⟩, 4)], 120, 0⟩,
    ⟨[(⟨152, by decide⟩, 2), (⟨182, by decide⟩, 4), (⟨183, by decide⟩, 4), (⟨233, by decide⟩, 4), (⟨311, by decide⟩, 4), (⟨367, by decide⟩, 2)], 120, 0⟩]

private def fourRowFiniteCoefficientRowDataChunk2 : Array (FourRowFiniteCoefficientRow) :=
  #[⟨[(⟨153, by decide⟩, 2), (⟨184, by decide⟩, 4), (⟨235, by decide⟩, 2), (⟨242, by decide⟩, 4), (⟨244, by decide⟩, 2), (⟨321, by decide⟩, 2), (⟨368, by decide⟩, 4)], 120, 48⟩,
    ⟨[(⟨155, by decide⟩, 2), (⟨241, by decide⟩, 12), (⟨260, by decide⟩, 6)], 120, 120⟩,
    ⟨[(⟨156, by decide⟩, 2), (⟨243, by decide⟩, 12), (⟨344, by decide⟩, 6)], 120, 48⟩,
    ⟨[(⟨157, by decide⟩, 2), (⟨245, by decide⟩, 12), (⟨379, by decide⟩, 6)], 120, 120⟩,
    ⟨[(⟨193, by decide⟩, 4), (⟨194, by decide⟩, 4), (⟨203, by decide⟩, 4), (⟨289, by decide⟩, 2), (⟨312, by decide⟩, 2), (⟨314, by decide⟩, 4)], 120, 0⟩,
    ⟨[(⟨195, by decide⟩, 8), (⟨266, by decide⟩, 4), (⟨322, by decide⟩, 4), (⟨369, by decide⟩, 4)], 120, 0⟩,
    ⟨[(⟨198, by decide⟩, 4), (⟨204, by decide⟩, 4), (⟨250, by decide⟩, 4), (⟨290, by decide⟩, 2), (⟨324, by decide⟩, 4), (⟨372, by decide⟩, 2)], 120, 0⟩,
    ⟨[(⟨199, by decide⟩, 2), (⟨200, by decide⟩, 2), (⟨209, by decide⟩, 2), (⟨251, by decide⟩, 2), (⟨252, by decide⟩, 2), (⟨267, by decide⟩, 2), (⟨313, by decide⟩, 2), (⟨316, by decide⟩, 2), (⟨326, by decide⟩, 2), (⟨370, by decide⟩, 2)], 120, 0⟩,
    ⟨[(⟨201, by decide⟩, 4), (⟨253, by decide⟩, 4), (⟨268, by decide⟩, 4), (⟨323, by decide⟩, 2), (⟨371, by decide⟩, 4), (⟨380, by decide⟩, 2)], 120, 48⟩,
    ⟨[(⟨205, by decide⟩, 6), (⟨291, by decide⟩, 6), (⟨295, by decide⟩, 2), (⟨335, by decide⟩, 6)], 120, 48⟩,
    ⟨[(⟨206, by decide⟩, 4), (⟨210, by decide⟩, 2), (⟨292, by decide⟩, 2), (⟨317, by decide⟩, 4), (⟨318, by decide⟩, 4), (⟨336, by decide⟩, 2), (⟨350, by decide⟩, 2)], 120, 48⟩,
    ⟨[(⟨207, by decide⟩, 4), (⟨269, by decide⟩, 2), (⟨293, by decide⟩, 2), (⟨328, by decide⟩, 4), (⟨337, by decide⟩, 2), (⟨351, by decide⟩, 2), (⟨375, by decide⟩, 4)], 120, 48⟩,
    ⟨[(⟨211, by decide⟩, 4), (⟨270, by decide⟩, 2), (⟨319, by decide⟩, 4), (⟨330, by decide⟩, 4), (⟨374, by decide⟩, 4), (⟨387, by decide⟩, 2)], 120, 48⟩,
    ⟨[(⟨213, by decide⟩, 2), (⟨261, by decide⟩, 4), (⟨262, by decide⟩, 2), (⟨263, by decide⟩, 2), (⟨274, by decide⟩, 2), (⟨327, by decide⟩, 4), (⟨373, by decide⟩, 4)], 120, 48⟩,
    ⟨[(⟨214, by decide⟩, 2), (⟨271, by decide⟩, 4), (⟨329, by decide⟩, 4), (⟨346, by decide⟩, 2), (⟨347, by decide⟩, 2), (⟨353, by decide⟩, 2), (⟨376, by decide⟩, 4)], 120, 48⟩,
    ⟨[(⟨215, by decide⟩, 2), (⟨272, by decide⟩, 4), (⟨331, by decide⟩, 4), (⟨377, by decide⟩, 4), (⟨382, by decide⟩, 2), (⟨384, by decide⟩, 2), (⟨388, by decide⟩, 2)], 120, 72⟩,
    ⟨[(⟨264, by decide⟩, 8), (⟨278, by decide⟩, 4), (⟨381, by decide⟩, 8)], 120, 120⟩,
    ⟨[(⟨275, by decide⟩, 6), (⟨297, by decide⟩, 2), (⟨345, by decide⟩, 12)], 120, 48⟩,
    ⟨[(⟨276, by decide⟩, 4), (⟨279, by decide⟩, 2), (⟨348, by decide⟩, 4), (⟨355, by decide⟩, 2), (⟨383, by decide⟩, 8)], 120, 96⟩,
    ⟨[(⟨280, by decide⟩, 6), (⟨385, by decide⟩, 12), (⟨390, by decide⟩, 2)], 120, 120⟩]

private def fourRowFiniteCoefficientRowDataChunks : Array (Array (FourRowFiniteCoefficientRow)) :=
  #[fourRowFiniteCoefficientRowDataChunk0, fourRowFiniteCoefficientRowDataChunk1, fourRowFiniteCoefficientRowDataChunk2]

def fourRowFiniteCoefficientRowData (i : ℕ) : FourRowFiniteCoefficientRow :=
  (fourRowFiniteCoefficientRowDataChunks.getD (i / 32) #[]).getD (i % 32) (default)

def fourRowFiniteCoefficientRows (e : Fin 84) : FourRowFiniteCoefficientRow :=
  fourRowFiniteCoefficientRowData e.val

private def fourRowFiniteKernelRowDataChunk0 : Array (List FourRowFiniteKernelTerm) :=
  #[[⟨⟨0, by decide⟩, 0, 1⟩, ⟨⟨1, by decide⟩, 1, -1⟩, ⟨⟨2, by decide⟩, 0, 3⟩, ⟨⟨3, by decide⟩, 3, -3⟩],
    [⟨⟨1, by decide⟩, 0, 1⟩, ⟨⟨4, by decide⟩, 0, 1⟩, ⟨⟨5, by decide⟩, 1, -2⟩, ⟨⟨6, by decide⟩, 0, 3⟩, ⟨⟨7, by decide⟩, 0, 3⟩, ⟨⟨8, by decide⟩, 3, -6⟩],
    [⟨⟨2, by decide⟩, 0, 1⟩, ⟨⟨6, by decide⟩, 1, -1⟩, ⟨⟨9, by decide⟩, 0, 1⟩, ⟨⟨10, by decide⟩, 1, -1⟩, ⟨⟨11, by decide⟩, 0, 2⟩, ⟨⟨12, by decide⟩, 2, -2⟩],
    [⟨⟨3, by decide⟩, 0, 1⟩, ⟨⟨7, by decide⟩, 0, 1⟩, ⟨⟨8, by decide⟩, 1, -2⟩, ⟨⟨10, by decide⟩, 0, 1⟩, ⟨⟨12, by decide⟩, 0, 2⟩, ⟨⟨13, by decide⟩, 0, 1⟩, ⟨⟨14, by decide⟩, 1, -2⟩, ⟨⟨15, by decide⟩, 0, 2⟩, ⟨⟨16, by decide⟩, 2, -4⟩],
    [⟨⟨17, by decide⟩, 0, 1⟩, ⟨⟨18, by decide⟩, 0, 1⟩, ⟨⟨19, by decide⟩, 1, -2⟩, ⟨⟨20, by decide⟩, 0, 3⟩, ⟨⟨21, by decide⟩, 0, 3⟩, ⟨⟨22, by decide⟩, 3, -6⟩],
    [⟨⟨18, by decide⟩, 0, 1⟩, ⟨⟨23, by decide⟩, 0, 1⟩, ⟨⟨24, by decide⟩, 1, -2⟩, ⟨⟨25, by decide⟩, 0, 3⟩, ⟨⟨26, by decide⟩, 0, 3⟩, ⟨⟨27, by decide⟩, 3, -6⟩],
    [⟨⟨19, by decide⟩, 0, 1⟩, ⟨⟨24, by decide⟩, 0, 1⟩, ⟨⟨28, by decide⟩, 0, 1⟩, ⟨⟨29, by decide⟩, 1, -3⟩, ⟨⟨30, by decide⟩, 0, 3⟩, ⟨⟨31, by decide⟩, 0, 3⟩, ⟨⟨32, by decide⟩, 0, 3⟩, ⟨⟨33, by decide⟩, 3, -9⟩],
    [⟨⟨20, by decide⟩, 0, 1⟩, ⟨⟨25, by decide⟩, 0, 1⟩, ⟨⟨30, by decide⟩, 1, -2⟩, ⟨⟨34, by decide⟩, 0, 1⟩, ⟨⟨35, by decide⟩, 0, 1⟩, ⟨⟨36, by decide⟩, 1, -2⟩, ⟨⟨37, by decide⟩, 0, 2⟩, ⟨⟨38, by decide⟩, 0, 2⟩, ⟨⟨39, by decide⟩, 2, -4⟩],
    [⟨⟨21, by decide⟩, 0, 1⟩, ⟨⟨26, by decide⟩, 0, 1⟩, ⟨⟨31, by decide⟩, 1, -2⟩, ⟨⟨35, by decide⟩, 0, 1⟩, ⟨⟨38, by decide⟩, 0, 2⟩, ⟨⟨40, by decide⟩, 0, 1⟩, ⟨⟨41, by decide⟩, 1, -2⟩, ⟨⟨42, by decide⟩, 0, 2⟩, ⟨⟨43, by decide⟩, 2, -4⟩],
    [⟨⟨22, by decide⟩, 0, 1⟩, ⟨⟨27, by decide⟩, 0, 1⟩, ⟨⟨32, by decide⟩, 0, 1⟩, ⟨⟨33, by decide⟩, 1, -3⟩, ⟨⟨36, by decide⟩, 0, 1⟩, ⟨⟨39, by decide⟩, 0, 2⟩, ⟨⟨41, by decide⟩, 0, 1⟩, ⟨⟨43, by decide⟩, 0, 2⟩, ⟨⟨44, by decide⟩, 0, 1⟩, ⟨⟨45, by decide⟩, 1, -3⟩, ⟨⟨46, by decide⟩, 0, 2⟩, ⟨⟨47, by decide⟩, 2, -6⟩],
    [⟨⟨48, by decide⟩, 0, 1⟩, ⟨⟨49, by decide⟩, 1, -1⟩, ⟨⟨50, by decide⟩, 0, 1⟩, ⟨⟨51, by decide⟩, 1, -1⟩, ⟨⟨52, by decide⟩, 0, 2⟩, ⟨⟨53, by decide⟩, 2, -2⟩],
    [⟨⟨49, by decide⟩, 0, 1⟩, ⟨⟨54, by decide⟩, 0, 1⟩, ⟨⟨55, by decide⟩, 1, -2⟩, ⟨⟨56, by decide⟩, 0, 1⟩, ⟨⟨57, by decide⟩, 0, 1⟩, ⟨⟨58, by decide⟩, 1, -2⟩, ⟨⟨59, by decide⟩, 0, 2⟩, ⟨⟨60, by decide⟩, 0, 2⟩, ⟨⟨61, by decide⟩, 2, -4⟩],
    [⟨⟨50, by decide⟩, 0, 1⟩, ⟨⟨56, by decide⟩, 1, -1⟩, ⟨⟨62, by decide⟩, 0, 1⟩, ⟨⟨63, by decide⟩, 1, -1⟩, ⟨⟨64, by decide⟩, 0, 2⟩, ⟨⟨65, by decide⟩, 2, -2⟩],
    [⟨⟨51, by decide⟩, 0, 1⟩, ⟨⟨57, by decide⟩, 0, 1⟩, ⟨⟨58, by decide⟩, 1, -2⟩, ⟨⟨63, by decide⟩, 0, 1⟩, ⟨⟨66, by decide⟩, 0, 1⟩, ⟨⟨67, by decide⟩, 1, -2⟩, ⟨⟨68, by decide⟩, 0, 2⟩, ⟨⟨69, by decide⟩, 0, 2⟩, ⟨⟨70, by decide⟩, 2, -4⟩],
    [⟨⟨52, by decide⟩, 0, 1⟩, ⟨⟨59, by decide⟩, 1, -1⟩, ⟨⟨64, by decide⟩, 0, 1⟩, ⟨⟨68, by decide⟩, 1, -1⟩, ⟨⟨71, by decide⟩, 0, 1⟩, ⟨⟨72, by decide⟩, 1, -1⟩, ⟨⟨73, by decide⟩, 0, 1⟩, ⟨⟨74, by decide⟩, 1, -1⟩],
    [⟨⟨53, by decide⟩, 0, 1⟩, ⟨⟨60, by decide⟩, 0, 1⟩, ⟨⟨61, by decide⟩, 1, -2⟩, ⟨⟨65, by decide⟩, 0, 1⟩, ⟨⟨69, by decide⟩, 0, 1⟩, ⟨⟨70, by decide⟩, 1, -2⟩, ⟨⟨72, by decide⟩, 0, 1⟩, ⟨⟨74, by decide⟩, 0, 1⟩, ⟨⟨75, by decide⟩, 0, 1⟩, ⟨⟨76, by decide⟩, 1, -2⟩, ⟨⟨77, by decide⟩, 0, 1⟩, ⟨⟨78, by decide⟩, 1, -2⟩],
    [⟨⟨79, by decide⟩, 0, 1⟩, ⟨⟨80, by decide⟩, 0, 1⟩, ⟨⟨81, by decide⟩, 1, -2⟩, ⟨⟨82, by decide⟩, 0, 1⟩, ⟨⟨83, by decide⟩, 0, 1⟩, ⟨⟨84, by decide⟩, 1, -2⟩, ⟨⟨85, by decide⟩, 0, 2⟩, ⟨⟨86, by decide⟩, 0, 2⟩, ⟨⟨87, by decide⟩, 2, -4⟩],
    [⟨⟨80, by decide⟩, 0, 1⟩, ⟨⟨88, by decide⟩, 0, 1⟩, ⟨⟨89, by decide⟩, 1, -2⟩, ⟨⟨90, by decide⟩, 0, 1⟩, ⟨⟨91, by decide⟩, 0, 1⟩, ⟨⟨92, by decide⟩, 1, -2⟩, ⟨⟨93, by decide⟩, 0, 2⟩, ⟨⟨94, by decide⟩, 0, 2⟩, ⟨⟨95, by decide⟩, 2, -4⟩],
    [⟨⟨81, by decide⟩, 0, 1⟩, ⟨⟨89, by decide⟩, 0, 1⟩, ⟨⟨96, by decide⟩, 0, 1⟩, ⟨⟨97, by decide⟩, 1, -3⟩, ⟨⟨98, by decide⟩, 0, 1⟩, ⟨⟨99, by decide⟩, 0, 1⟩, ⟨⟨100, by decide⟩, 0, 1⟩, ⟨⟨101, by decide⟩, 1, -3⟩, ⟨⟨102, by decide⟩, 0, 2⟩, ⟨⟨103, by decide⟩, 0, 2⟩, ⟨⟨104, by decide⟩, 0, 2⟩, ⟨⟨105, by decide⟩, 2, -6⟩],
    [⟨⟨82, by decide⟩, 0, 1⟩, ⟨⟨90, by decide⟩, 0, 1⟩, ⟨⟨98, by decide⟩, 1, -2⟩, ⟨⟨106, by decide⟩, 0, 1⟩, ⟨⟨107, by decide⟩, 0, 1⟩, ⟨⟨108, by decide⟩, 1, -2⟩, ⟨⟨109, by decide⟩, 0, 2⟩, ⟨⟨110, by decide⟩, 0, 2⟩, ⟨⟨111, by decide⟩, 2, -4⟩],
    [⟨⟨83, by decide⟩, 0, 1⟩, ⟨⟨91, by decide⟩, 0, 1⟩, ⟨⟨99, by decide⟩, 1, -2⟩, ⟨⟨107, by decide⟩, 0, 1⟩, ⟨⟨112, by decide⟩, 0, 1⟩, ⟨⟨113, by decide⟩, 1, -2⟩, ⟨⟨114, by decide⟩, 0, 2⟩, ⟨⟨115, by decide⟩, 0, 2⟩, ⟨⟨116, by decide⟩, 2, -4⟩],
    [⟨⟨84, by decide⟩, 0, 1⟩, ⟨⟨92, by decide⟩, 0, 1⟩, ⟨⟨100, by decide⟩, 0, 1⟩, ⟨⟨101, by decide⟩, 1, -3⟩, ⟨⟨108, by decide⟩, 0, 1⟩, ⟨⟨113, by decide⟩, 0, 1⟩, ⟨⟨117, by decide⟩, 0, 1⟩, ⟨⟨118, by decide⟩, 1, -3⟩, ⟨⟨119, by decide⟩, 0, 2⟩, ⟨⟨120, by decide⟩, 0, 2⟩, ⟨⟨121, by decide⟩, 0, 2⟩, ⟨⟨122, by decide⟩, 2, -6⟩],
    [⟨⟨85, by decide⟩, 0, 1⟩, ⟨⟨93, by decide⟩, 0, 1⟩, ⟨⟨102, by decide⟩, 1, -2⟩, ⟨⟨109, by decide⟩, 0, 1⟩, ⟨⟨114, by decide⟩, 0, 1⟩, ⟨⟨119, by decide⟩, 1, -2⟩, ⟨⟨123, by decide⟩, 0, 1⟩, ⟨⟨124, by decide⟩, 0, 1⟩, ⟨⟨125, by decide⟩, 1, -2⟩, ⟨⟨126, by decide⟩, 0, 1⟩, ⟨⟨127, by decide⟩, 0, 1⟩, ⟨⟨128, by decide⟩, 1, -2⟩],
    [⟨⟨86, by decide⟩, 0, 1⟩, ⟨⟨94, by decide⟩, 0, 1⟩, ⟨⟨103, by decide⟩, 1, -2⟩, ⟨⟨110, by decide⟩, 0, 1⟩, ⟨⟨115, by decide⟩, 0, 1⟩, ⟨⟨120, by decide⟩, 1, -2⟩, ⟨⟨124, by decide⟩, 0, 1⟩, ⟨⟨127, by decide⟩, 0, 1⟩, ⟨⟨129, by decide⟩, 0, 1⟩, ⟨⟨130, by decide⟩, 1, -2⟩, ⟨⟨131, by decide⟩, 0, 1⟩, ⟨⟨132, by decide⟩, 1, -2⟩],
    [⟨⟨87, by decide⟩, 0, 1⟩, ⟨⟨95, by decide⟩, 0, 1⟩, ⟨⟨104, by decide⟩, 0, 1⟩, ⟨⟨105, by decide⟩, 1, -3⟩, ⟨⟨111, by decide⟩, 0, 1⟩, ⟨⟨116, by decide⟩, 0, 1⟩, ⟨⟨121, by decide⟩, 0, 1⟩, ⟨⟨122, by decide⟩, 1, -3⟩, ⟨⟨125, by decide⟩, 0, 1⟩, ⟨⟨128, by decide⟩, 0, 1⟩, ⟨⟨130, by decide⟩, 0, 1⟩, ⟨⟨132, by decide⟩, 0, 1⟩, ⟨⟨133, by decide⟩, 0, 1⟩, ⟨⟨134, by decide⟩, 1, -3⟩, ⟨⟨135, by decide⟩, 0, 1⟩, ⟨⟨136, by decide⟩, 1, -3⟩],
    [⟨⟨137, by decide⟩, 0, 1⟩, ⟨⟨138, by decide⟩, 0, 2⟩, ⟨⟨139, by decide⟩, 1, -3⟩, ⟨⟨140, by decide⟩, 0, 3⟩, ⟨⟨141, by decide⟩, 0, 6⟩, ⟨⟨142, by decide⟩, 3, -9⟩],
    [⟨⟨139, by decide⟩, 0, 3⟩, ⟨⟨143, by decide⟩, 0, 1⟩, ⟨⟨144, by decide⟩, 1, -4⟩, ⟨⟨145, by decide⟩, 0, 9⟩, ⟨⟨146, by decide⟩, 0, 3⟩, ⟨⟨147, by decide⟩, 3, -12⟩],
    [⟨⟨140, by decide⟩, 0, 1⟩, ⟨⟨141, by decide⟩, 0, 2⟩, ⟨⟨145, by decide⟩, 1, -3⟩, ⟨⟨148, by decide⟩, 0, 1⟩, ⟨⟨149, by decide⟩, 0, 2⟩, ⟨⟨150, by decide⟩, 1, -3⟩, ⟨⟨151, by decide⟩, 0, 2⟩, ⟨⟨152, by decide⟩, 0, 4⟩, ⟨⟨153, by decide⟩, 2, -6⟩],
    [⟨⟨142, by decide⟩, 0, 3⟩, ⟨⟨146, by decide⟩, 0, 1⟩, ⟨⟨147, by decide⟩, 1, -4⟩, ⟨⟨150, by decide⟩, 0, 3⟩, ⟨⟨153, by decide⟩, 0, 6⟩, ⟨⟨154, by decide⟩, 0, 1⟩, ⟨⟨155, by decide⟩, 1, -4⟩, ⟨⟨156, by decide⟩, 0, 2⟩, ⟨⟨157, by decide⟩, 2, -8⟩],
    [⟨⟨158, by decide⟩, 0, 1⟩, ⟨⟨159, by decide⟩, 0, 1⟩, ⟨⟨160, by decide⟩, 1, -2⟩, ⟨⟨161, by decide⟩, 0, 1⟩, ⟨⟨162, by decide⟩, 0, 1⟩, ⟨⟨163, by decide⟩, 1, -2⟩, ⟨⟨164, by decide⟩, 0, 2⟩, ⟨⟨165, by decide⟩, 0, 2⟩, ⟨⟨166, by decide⟩, 2, -4⟩],
    [⟨⟨159, by decide⟩, 0, 1⟩, ⟨⟨167, by decide⟩, 0, 1⟩, ⟨⟨168, by decide⟩, 1, -2⟩, ⟨⟨169, by decide⟩, 0, 1⟩, ⟨⟨170, by decide⟩, 0, 1⟩, ⟨⟨171, by decide⟩, 1, -2⟩, ⟨⟨172, by decide⟩, 0, 2⟩, ⟨⟨173, by decide⟩, 0, 2⟩, ⟨⟨174, by decide⟩, 2, -4⟩],
    [⟨⟨160, by decide⟩, 0, 1⟩, ⟨⟨168, by decide⟩, 0, 1⟩, ⟨⟨175, by decide⟩, 0, 1⟩, ⟨⟨176, by decide⟩, 1, -3⟩, ⟨⟨177, by decide⟩, 0, 1⟩, ⟨⟨178, by decide⟩, 0, 1⟩, ⟨⟨179, by decide⟩, 0, 1⟩, ⟨⟨180, by decide⟩, 1, -3⟩, ⟨⟨181, by decide⟩, 0, 2⟩, ⟨⟨182, by decide⟩, 0, 2⟩, ⟨⟨183, by decide⟩, 0, 2⟩, ⟨⟨184, by decide⟩, 2, -6⟩]]

private def fourRowFiniteKernelRowDataChunk1 : Array (List FourRowFiniteKernelTerm) :=
  #[[⟨⟨161, by decide⟩, 0, 1⟩, ⟨⟨169, by decide⟩, 0, 1⟩, ⟨⟨177, by decide⟩, 1, -2⟩, ⟨⟨185, by decide⟩, 0, 1⟩, ⟨⟨186, by decide⟩, 0, 1⟩, ⟨⟨187, by decide⟩, 1, -2⟩, ⟨⟨188, by decide⟩, 0, 2⟩, ⟨⟨189, by decide⟩, 0, 2⟩, ⟨⟨190, by decide⟩, 2, -4⟩],
    [⟨⟨162, by decide⟩, 0, 1⟩, ⟨⟨170, by decide⟩, 0, 1⟩, ⟨⟨178, by decide⟩, 1, -2⟩, ⟨⟨186, by decide⟩, 0, 1⟩, ⟨⟨191, by decide⟩, 0, 1⟩, ⟨⟨192, by decide⟩, 1, -2⟩, ⟨⟨193, by decide⟩, 0, 2⟩, ⟨⟨194, by decide⟩, 0, 2⟩, ⟨⟨195, by decide⟩, 2, -4⟩],
    [⟨⟨163, by decide⟩, 0, 1⟩, ⟨⟨171, by decide⟩, 0, 1⟩, ⟨⟨179, by decide⟩, 0, 1⟩, ⟨⟨180, by decide⟩, 1, -3⟩, ⟨⟨187, by decide⟩, 0, 1⟩, ⟨⟨192, by decide⟩, 0, 1⟩, ⟨⟨196, by decide⟩, 0, 1⟩, ⟨⟨197, by decide⟩, 1, -3⟩, ⟨⟨198, by decide⟩, 0, 2⟩, ⟨⟨199, by decide⟩, 0, 2⟩, ⟨⟨200, by decide⟩, 0, 2⟩, ⟨⟨201, by decide⟩, 2, -6⟩],
    [⟨⟨164, by decide⟩, 0, 1⟩, ⟨⟨172, by decide⟩, 0, 1⟩, ⟨⟨181, by decide⟩, 1, -2⟩, ⟨⟨188, by decide⟩, 0, 1⟩, ⟨⟨193, by decide⟩, 0, 1⟩, ⟨⟨198, by decide⟩, 1, -2⟩, ⟨⟨202, by decide⟩, 0, 1⟩, ⟨⟨203, by decide⟩, 0, 1⟩, ⟨⟨204, by decide⟩, 1, -2⟩, ⟨⟨205, by decide⟩, 0, 1⟩, ⟨⟨206, by decide⟩, 0, 1⟩, ⟨⟨207, by decide⟩, 1, -2⟩],
    [⟨⟨165, by decide⟩, 0, 1⟩, ⟨⟨173, by decide⟩, 0, 1⟩, ⟨⟨182, by decide⟩, 1, -2⟩, ⟨⟨189, by decide⟩, 0, 1⟩, ⟨⟨194, by decide⟩, 0, 1⟩, ⟨⟨199, by decide⟩, 1, -2⟩, ⟨⟨203, by decide⟩, 0, 1⟩, ⟨⟨206, by decide⟩, 0, 1⟩, ⟨⟨208, by decide⟩, 0, 1⟩, ⟨⟨209, by decide⟩, 1, -2⟩, ⟨⟨210, by decide⟩, 0, 1⟩, ⟨⟨211, by decide⟩, 1, -2⟩],
    [⟨⟨166, by decide⟩, 0, 1⟩, ⟨⟨174, by decide⟩, 0, 1⟩, ⟨⟨183, by decide⟩, 0, 1⟩, ⟨⟨184, by decide⟩, 1, -3⟩, ⟨⟨190, by decide⟩, 0, 1⟩, ⟨⟨195, by decide⟩, 0, 1⟩, ⟨⟨200, by decide⟩, 0, 1⟩, ⟨⟨201, by decide⟩, 1, -3⟩, ⟨⟨204, by decide⟩, 0, 1⟩, ⟨⟨207, by decide⟩, 0, 1⟩, ⟨⟨209, by decide⟩, 0, 1⟩, ⟨⟨211, by decide⟩, 0, 1⟩, ⟨⟨212, by decide⟩, 0, 1⟩, ⟨⟨213, by decide⟩, 1, -3⟩, ⟨⟨214, by decide⟩, 0, 1⟩, ⟨⟨215, by decide⟩, 1, -3⟩],
    [⟨⟨216, by decide⟩, 0, 1⟩, ⟨⟨217, by decide⟩, 0, 1⟩, ⟨⟨218, by decide⟩, 0, 1⟩, ⟨⟨219, by decide⟩, 1, -3⟩, ⟨⟨220, by decide⟩, 0, 1⟩, ⟨⟨221, by decide⟩, 0, 1⟩, ⟨⟨222, by decide⟩, 0, 1⟩, ⟨⟨223, by decide⟩, 1, -3⟩, ⟨⟨224, by decide⟩, 0, 2⟩, ⟨⟨225, by decide⟩, 0, 2⟩, ⟨⟨226, by decide⟩, 0, 2⟩, ⟨⟨227, by decide⟩, 2, -6⟩],
    [⟨⟨218, by decide⟩, 0, 2⟩, ⟨⟨228, by decide⟩, 0, 1⟩, ⟨⟨229, by decide⟩, 1, -3⟩, ⟨⟨230, by decide⟩, 0, 2⟩, ⟨⟨231, by decide⟩, 0, 1⟩, ⟨⟨232, by decide⟩, 1, -3⟩, ⟨⟨233, by decide⟩, 0, 4⟩, ⟨⟨234, by decide⟩, 0, 2⟩, ⟨⟨235, by decide⟩, 2, -6⟩],
    [⟨⟨219, by decide⟩, 0, 2⟩, ⟨⟨229, by decide⟩, 0, 1⟩, ⟨⟨236, by decide⟩, 0, 1⟩, ⟨⟨237, by decide⟩, 1, -4⟩, ⟨⟨238, by decide⟩, 0, 2⟩, ⟨⟨239, by decide⟩, 0, 1⟩, ⟨⟨240, by decide⟩, 0, 1⟩, ⟨⟨241, by decide⟩, 1, -4⟩, ⟨⟨242, by decide⟩, 0, 4⟩, ⟨⟨243, by decide⟩, 0, 2⟩, ⟨⟨244, by decide⟩, 0, 2⟩, ⟨⟨245, by decide⟩, 2, -8⟩],
    [⟨⟨220, by decide⟩, 0, 1⟩, ⟨⟨221, by decide⟩, 0, 1⟩, ⟨⟨230, by decide⟩, 0, 1⟩, ⟨⟨238, by decide⟩, 1, -3⟩, ⟨⟨246, by decide⟩, 0, 1⟩, ⟨⟨247, by decide⟩, 0, 1⟩, ⟨⟨248, by decide⟩, 0, 1⟩, ⟨⟨249, by decide⟩, 1, -3⟩, ⟨⟨250, by decide⟩, 0, 2⟩, ⟨⟨251, by decide⟩, 0, 2⟩, ⟨⟨252, by decide⟩, 0, 2⟩, ⟨⟨253, by decide⟩, 2, -6⟩],
    [⟨⟨222, by decide⟩, 0, 2⟩, ⟨⟨231, by decide⟩, 0, 1⟩, ⟨⟨239, by decide⟩, 1, -3⟩, ⟨⟨248, by decide⟩, 0, 2⟩, ⟨⟨254, by decide⟩, 0, 1⟩, ⟨⟨255, by decide⟩, 1, -3⟩, ⟨⟨256, by decide⟩, 0, 4⟩, ⟨⟨257, by decide⟩, 0, 2⟩, ⟨⟨258, by decide⟩, 2, -6⟩],
    [⟨⟨223, by decide⟩, 0, 2⟩, ⟨⟨232, by decide⟩, 0, 1⟩, ⟨⟨240, by decide⟩, 0, 1⟩, ⟨⟨241, by decide⟩, 1, -4⟩, ⟨⟨249, by decide⟩, 0, 2⟩, ⟨⟨255, by decide⟩, 0, 1⟩, ⟨⟨259, by decide⟩, 0, 1⟩, ⟨⟨260, by decide⟩, 1, -4⟩, ⟨⟨261, by decide⟩, 0, 4⟩, ⟨⟨262, by decide⟩, 0, 2⟩, ⟨⟨263, by decide⟩, 0, 2⟩, ⟨⟨264, by decide⟩, 2, -8⟩],
    [⟨⟨224, by decide⟩, 0, 1⟩, ⟨⟨225, by decide⟩, 0, 1⟩, ⟨⟨233, by decide⟩, 0, 1⟩, ⟨⟨242, by decide⟩, 1, -3⟩, ⟨⟨250, by decide⟩, 0, 1⟩, ⟨⟨251, by decide⟩, 0, 1⟩, ⟨⟨256, by decide⟩, 0, 1⟩, ⟨⟨261, by decide⟩, 1, -3⟩, ⟨⟨265, by decide⟩, 0, 1⟩, ⟨⟨266, by decide⟩, 0, 1⟩, ⟨⟨267, by decide⟩, 0, 1⟩, ⟨⟨268, by decide⟩, 1, -3⟩, ⟨⟨269, by decide⟩, 0, 1⟩, ⟨⟨270, by decide⟩, 0, 1⟩, ⟨⟨271, by decide⟩, 0, 1⟩, ⟨⟨272, by decide⟩, 1, -3⟩],
    [⟨⟨226, by decide⟩, 0, 2⟩, ⟨⟨234, by decide⟩, 0, 1⟩, ⟨⟨243, by decide⟩, 1, -3⟩, ⟨⟨252, by decide⟩, 0, 2⟩, ⟨⟨257, by decide⟩, 0, 1⟩, ⟨⟨262, by decide⟩, 1, -3⟩, ⟨⟨267, by decide⟩, 0, 2⟩, ⟨⟨271, by decide⟩, 0, 2⟩, ⟨⟨273, by decide⟩, 0, 1⟩, ⟨⟨274, by decide⟩, 1, -3⟩, ⟨⟨275, by decide⟩, 0, 1⟩, ⟨⟨276, by decide⟩, 1, -3⟩],
    [⟨⟨227, by decide⟩, 0, 2⟩, ⟨⟨235, by decide⟩, 0, 1⟩, ⟨⟨244, by decide⟩, 0, 1⟩, ⟨⟨245, by decide⟩, 1, -4⟩, ⟨⟨253, by decide⟩, 0, 2⟩, ⟨⟨258, by decide⟩, 0, 1⟩, ⟨⟨263, by decide⟩, 0, 1⟩, ⟨⟨264, by decide⟩, 1, -4⟩, ⟨⟨268, by decide⟩, 0, 2⟩, ⟨⟨272, by decide⟩, 0, 2⟩, ⟨⟨274, by decide⟩, 0, 1⟩, ⟨⟨276, by decide⟩, 0, 1⟩, ⟨⟨277, by decide⟩, 0, 1⟩, ⟨⟨278, by decide⟩, 1, -4⟩, ⟨⟨279, by decide⟩, 0, 1⟩, ⟨⟨280, by decide⟩, 1, -4⟩],
    [⟨⟨281, by decide⟩, 0, 1⟩, ⟨⟨282, by decide⟩, 1, -1⟩, ⟨⟨283, by decide⟩, 0, 2⟩, ⟨⟨284, by decide⟩, 2, -2⟩, ⟨⟨285, by decide⟩, 0, 1⟩, ⟨⟨286, by decide⟩, 1, -1⟩],
    [⟨⟨282, by decide⟩, 0, 1⟩, ⟨⟨284, by decide⟩, 0, 2⟩, ⟨⟨287, by decide⟩, 0, 1⟩, ⟨⟨288, by decide⟩, 1, -2⟩, ⟨⟨289, by decide⟩, 0, 2⟩, ⟨⟨290, by decide⟩, 2, -4⟩, ⟨⟨291, by decide⟩, 0, 1⟩, ⟨⟨292, by decide⟩, 0, 1⟩, ⟨⟨293, by decide⟩, 1, -2⟩],
    [⟨⟨285, by decide⟩, 0, 3⟩, ⟨⟨291, by decide⟩, 3, -3⟩, ⟨⟨294, by decide⟩, 0, 1⟩, ⟨⟨295, by decide⟩, 1, -1⟩],
    [⟨⟨286, by decide⟩, 0, 3⟩, ⟨⟨292, by decide⟩, 0, 3⟩, ⟨⟨293, by decide⟩, 3, -6⟩, ⟨⟨295, by decide⟩, 0, 1⟩, ⟨⟨296, by decide⟩, 0, 1⟩, ⟨⟨297, by decide⟩, 1, -2⟩],
    [⟨⟨298, by decide⟩, 0, 1⟩, ⟨⟨299, by decide⟩, 0, 1⟩, ⟨⟨300, by decide⟩, 1, -2⟩, ⟨⟨301, by decide⟩, 0, 1⟩, ⟨⟨302, by decide⟩, 0, 1⟩, ⟨⟨303, by decide⟩, 1, -2⟩, ⟨⟨304, by decide⟩, 0, 1⟩, ⟨⟨305, by decide⟩, 0, 1⟩, ⟨⟨306, by decide⟩, 1, -2⟩, ⟨⟨307, by decide⟩, 0, 1⟩, ⟨⟨308, by decide⟩, 0, 1⟩, ⟨⟨309, by decide⟩, 1, -2⟩],
    [⟨⟨299, by decide⟩, 0, 1⟩, ⟨⟨302, by decide⟩, 0, 1⟩, ⟨⟨310, by decide⟩, 0, 1⟩, ⟨⟨311, by decide⟩, 1, -2⟩, ⟨⟨312, by decide⟩, 0, 1⟩, ⟨⟨313, by decide⟩, 1, -2⟩, ⟨⟨314, by decide⟩, 0, 1⟩, ⟨⟨315, by decide⟩, 0, 1⟩, ⟨⟨316, by decide⟩, 1, -2⟩, ⟨⟨317, by decide⟩, 0, 1⟩, ⟨⟨318, by decide⟩, 0, 1⟩, ⟨⟨319, by decide⟩, 1, -2⟩],
    [⟨⟨300, by decide⟩, 0, 1⟩, ⟨⟨303, by decide⟩, 0, 1⟩, ⟨⟨311, by decide⟩, 0, 1⟩, ⟨⟨313, by decide⟩, 0, 1⟩, ⟨⟨320, by decide⟩, 0, 1⟩, ⟨⟨321, by decide⟩, 1, -3⟩, ⟨⟨322, by decide⟩, 0, 1⟩, ⟨⟨323, by decide⟩, 1, -3⟩, ⟨⟨324, by decide⟩, 0, 1⟩, ⟨⟨325, by decide⟩, 0, 1⟩, ⟨⟨326, by decide⟩, 0, 1⟩, ⟨⟨327, by decide⟩, 1, -3⟩, ⟨⟨328, by decide⟩, 0, 1⟩, ⟨⟨329, by decide⟩, 0, 1⟩, ⟨⟨330, by decide⟩, 0, 1⟩, ⟨⟨331, by decide⟩, 1, -3⟩],
    [⟨⟨304, by decide⟩, 0, 2⟩, ⟨⟨314, by decide⟩, 0, 2⟩, ⟨⟨324, by decide⟩, 2, -4⟩, ⟨⟨332, by decide⟩, 0, 1⟩, ⟨⟨333, by decide⟩, 0, 1⟩, ⟨⟨334, by decide⟩, 1, -2⟩, ⟨⟨335, by decide⟩, 0, 1⟩, ⟨⟨336, by decide⟩, 0, 1⟩, ⟨⟨337, by decide⟩, 1, -2⟩],
    [⟨⟨305, by decide⟩, 0, 2⟩, ⟨⟨315, by decide⟩, 0, 2⟩, ⟨⟨325, by decide⟩, 2, -4⟩, ⟨⟨333, by decide⟩, 0, 1⟩, ⟨⟨338, by decide⟩, 0, 1⟩, ⟨⟨339, by decide⟩, 1, -2⟩, ⟨⟨340, by decide⟩, 0, 1⟩, ⟨⟨341, by decide⟩, 0, 1⟩, ⟨⟨342, by decide⟩, 1, -2⟩],
    [⟨⟨306, by decide⟩, 0, 2⟩, ⟨⟨316, by decide⟩, 0, 2⟩, ⟨⟨326, by decide⟩, 0, 2⟩, ⟨⟨327, by decide⟩, 2, -6⟩, ⟨⟨334, by decide⟩, 0, 1⟩, ⟨⟨339, by decide⟩, 0, 1⟩, ⟨⟨343, by decide⟩, 0, 1⟩, ⟨⟨344, by decide⟩, 1, -3⟩, ⟨⟨345, by decide⟩, 0, 1⟩, ⟨⟨346, by decide⟩, 0, 1⟩, ⟨⟨347, by decide⟩, 0, 1⟩, ⟨⟨348, by decide⟩, 1, -3⟩],
    [⟨⟨307, by decide⟩, 0, 2⟩, ⟨⟨317, by decide⟩, 0, 2⟩, ⟨⟨328, by decide⟩, 2, -4⟩, ⟨⟨335, by decide⟩, 0, 1⟩, ⟨⟨340, by decide⟩, 0, 1⟩, ⟨⟨345, by decide⟩, 1, -2⟩, ⟨⟨349, by decide⟩, 0, 1⟩, ⟨⟨350, by decide⟩, 0, 1⟩, ⟨⟨351, by decide⟩, 1, -2⟩],
    [⟨⟨308, by decide⟩, 0, 2⟩, ⟨⟨318, by decide⟩, 0, 2⟩, ⟨⟨329, by decide⟩, 2, -4⟩, ⟨⟨336, by decide⟩, 0, 1⟩, ⟨⟨341, by decide⟩, 0, 1⟩, ⟨⟨346, by decide⟩, 1, -2⟩, ⟨⟨350, by decide⟩, 0, 1⟩, ⟨⟨352, by decide⟩, 0, 1⟩, ⟨⟨353, by decide⟩, 1, -2⟩],
    [⟨⟨309, by decide⟩, 0, 2⟩, ⟨⟨319, by decide⟩, 0, 2⟩, ⟨⟨330, by decide⟩, 0, 2⟩, ⟨⟨331, by decide⟩, 2, -6⟩, ⟨⟨337, by decide⟩, 0, 1⟩, ⟨⟨342, by decide⟩, 0, 1⟩, ⟨⟨347, by decide⟩, 0, 1⟩, ⟨⟨348, by decide⟩, 1, -3⟩, ⟨⟨351, by decide⟩, 0, 1⟩, ⟨⟨353, by decide⟩, 0, 1⟩, ⟨⟨354, by decide⟩, 0, 1⟩, ⟨⟨355, by decide⟩, 1, -3⟩],
    [⟨⟨356, by decide⟩, 0, 1⟩, ⟨⟨357, by decide⟩, 0, 2⟩, ⟨⟨358, by decide⟩, 1, -3⟩, ⟨⟨359, by decide⟩, 0, 2⟩, ⟨⟨360, by decide⟩, 0, 2⟩, ⟨⟨361, by decide⟩, 0, 2⟩, ⟨⟨362, by decide⟩, 2, -6⟩, ⟨⟨363, by decide⟩, 0, 1⟩, ⟨⟨364, by decide⟩, 0, 2⟩, ⟨⟨365, by decide⟩, 1, -3⟩],
    [⟨⟨357, by decide⟩, 0, 1⟩, ⟨⟨359, by decide⟩, 0, 1⟩, ⟨⟨361, by decide⟩, 0, 1⟩, ⟨⟨366, by decide⟩, 0, 1⟩, ⟨⟨367, by decide⟩, 0, 1⟩, ⟨⟨368, by decide⟩, 1, -3⟩, ⟨⟨369, by decide⟩, 0, 1⟩, ⟨⟨370, by decide⟩, 0, 2⟩, ⟨⟨371, by decide⟩, 1, -3⟩, ⟨⟨372, by decide⟩, 0, 1⟩, ⟨⟨373, by decide⟩, 1, -3⟩, ⟨⟨374, by decide⟩, 0, 1⟩, ⟨⟨375, by decide⟩, 0, 1⟩, ⟨⟨376, by decide⟩, 0, 1⟩, ⟨⟨377, by decide⟩, 1, -3⟩],
    [⟨⟨358, by decide⟩, 0, 1⟩, ⟨⟨362, by decide⟩, 0, 2⟩, ⟨⟨368, by decide⟩, 0, 2⟩, ⟨⟨371, by decide⟩, 0, 2⟩, ⟨⟨373, by decide⟩, 0, 2⟩, ⟨⟨378, by decide⟩, 0, 1⟩, ⟨⟨379, by decide⟩, 1, -4⟩, ⟨⟨380, by decide⟩, 0, 2⟩, ⟨⟨381, by decide⟩, 2, -8⟩, ⟨⟨382, by decide⟩, 0, 1⟩, ⟨⟨383, by decide⟩, 0, 2⟩, ⟨⟨384, by decide⟩, 0, 1⟩, ⟨⟨385, by decide⟩, 1, -4⟩],
    [⟨⟨363, by decide⟩, 0, 1⟩, ⟨⟨364, by decide⟩, 0, 2⟩, ⟨⟨374, by decide⟩, 0, 2⟩, ⟨⟨375, by decide⟩, 0, 2⟩, ⟨⟨376, by decide⟩, 0, 2⟩, ⟨⟨382, by decide⟩, 1, -3⟩, ⟨⟨383, by decide⟩, 2, -6⟩, ⟨⟨386, by decide⟩, 0, 1⟩, ⟨⟨387, by decide⟩, 0, 2⟩, ⟨⟨388, by decide⟩, 1, -3⟩]]

private def fourRowFiniteKernelRowDataChunk2 : Array (List FourRowFiniteKernelTerm) :=
  #[[⟨⟨365, by decide⟩, 0, 3⟩, ⟨⟨377, by decide⟩, 0, 6⟩, ⟨⟨384, by decide⟩, 0, 3⟩, ⟨⟨385, by decide⟩, 3, -12⟩, ⟨⟨388, by decide⟩, 0, 3⟩, ⟨⟨389, by decide⟩, 0, 1⟩, ⟨⟨390, by decide⟩, 1, -4⟩]]

private def fourRowFiniteKernelRowDataChunks : Array (Array (List FourRowFiniteKernelTerm)) :=
  #[fourRowFiniteKernelRowDataChunk0, fourRowFiniteKernelRowDataChunk1, fourRowFiniteKernelRowDataChunk2]

def fourRowFiniteKernelRowData (i : ℕ) : List FourRowFiniteKernelTerm :=
  (fourRowFiniteKernelRowDataChunks.getD (i / 32) #[]).getD (i % 32) ([])

def fourRowFiniteKernelRows (e : Fin 65) : List FourRowFiniteKernelTerm :=
  fourRowFiniteKernelRowData e.val

end DittertRybin
