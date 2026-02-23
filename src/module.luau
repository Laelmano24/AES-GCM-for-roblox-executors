local Encryption = {
	AES = {},
}

local Utils = {
	CSPRNG = {},
	Conversions = {},
}

local Funcs = {
	ChaCha20 = nil,
	Blake3 = nil,
}

type AESModule = {
    Encrypt: (Plaintext: buffer, Key: buffer, IV: buffer, AAD: buffer?) -> (buffer, buffer),
    Decrypt: (Ciphertext: buffer, Key: buffer, IV: buffer, Tag: buffer, AAD: buffer?) -> (boolean, buffer?)
}

type EncryptionModule = {
    AES: AESModule
}

type ConversionsModule = {
    ToHex: (Buffer: buffer) -> string,
    FromHex: (Hex: string | buffer) -> buffer
}

type CSPRNGModule = {
	BlockExpansion: boolean,

	SizeTarget: number,
	RekeyAfter: number,

	Key: buffer,
	Nonce: buffer,
	Buffer: buffer,

	Counter: number,
	BufferPosition: number,
	BufferSize: number,
	BytesLeft: number,

	EntropyProviders: { EntropyProvider },

	Reseed: (CustomEntropy: buffer?) -> (),
	AddEntropyProvider: (ProviderFunction: EntropyProvider) -> (),
	RemoveEntropyProvider: (ProviderFunction: EntropyProvider) -> (),

	Random: () -> number,
	RandomInt: (Min: number, Max: number?) -> number,
	RandomNumber: (Min: number, Max: number?) -> number,
	RandomBytes: (Count: number) -> buffer,
	RandomString: (Length: number, AsBuffer: boolean?) -> string | buffer,
	RandomHex: (Length: number) -> string,
	Ed25519ClampedBytes: (Input: buffer) -> buffer,
	Ed25519Random: () -> buffer,
}

type typeCryptography = {
    Encryption: EncryptionModule,
    Funcs: {
        ChaCha20: (Data: buffer, Key: buffer, Nonce: buffer, Counter: number?, Rounds: number?) -> buffer,
		Blake3: (Message: buffer, Length: number?) -> buffer
    },
    Utils: {
		Conversions: ConversionsModule,
		CSPRNG: CSPRNGModule
	}
}

do
	--!strict
	--!optimize 2
	--!native

	local BLOCK_SIZE = 64
	local CV_SIZE = 32
	local EXTENDED_CV_SIZE = 64
	local MAX_STACK_DEPTH = 64
	local STACK_BUFFER_SIZE = MAX_STACK_DEPTH * CV_SIZE

	local CHUNK_START = 0x01
	local CHUNK_END = 0x02
	local PARENT_FLAG = 0x04
	local ROOT_FLAG = 0x08

	local INITIAL_VECTORS = buffer.create(CV_SIZE)
	do
		local IV = {
			0x6a09e667,
			0xbb67ae85,
			0x3c6ef372,
			0xa54ff53a,
			0x510e527f,
			0x9b05688c,
			0x1f83d9ab,
			0x5be0cd19,
		}
		for Index, Value in ipairs(IV) do
			buffer.writeu32(INITIAL_VECTORS, (Index - 1) * 4, Value)
		end
	end

	local function Compress(
		Hash: buffer,
		MessageBlock: buffer,
		Counter: number,
		V14: number,
		V15: number,
		IsFull: boolean?
	): buffer
		local Hash00 = buffer.readu32(Hash, 0)
		local Hash01 = buffer.readu32(Hash, 4)
		local Hash02 = buffer.readu32(Hash, 8)
		local Hash03 = buffer.readu32(Hash, 12)
		local Hash04 = buffer.readu32(Hash, 16)
		local Hash05 = buffer.readu32(Hash, 20)
		local Hash06 = buffer.readu32(Hash, 24)
		local Hash07 = buffer.readu32(Hash, 28)

		local V00, V01, V02, V03 = Hash00, Hash01, Hash02, Hash03
		local V04, V05, V06, V07 = Hash04, Hash05, Hash06, Hash07
		local V08, V09, V10, V11 = 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a

		local V12 = Counter % (2 ^ 32)
		local V13 = (Counter - V12) * (2 ^ -32)

		local M00 = buffer.readu32(MessageBlock, 0)
		local M01 = buffer.readu32(MessageBlock, 4)
		local M02 = buffer.readu32(MessageBlock, 8)
		local M03 = buffer.readu32(MessageBlock, 12)
		local M04 = buffer.readu32(MessageBlock, 16)
		local M05 = buffer.readu32(MessageBlock, 20)
		local M06 = buffer.readu32(MessageBlock, 24)
		local M07 = buffer.readu32(MessageBlock, 28)
		local M08 = buffer.readu32(MessageBlock, 32)
		local M09 = buffer.readu32(MessageBlock, 36)
		local M10 = buffer.readu32(MessageBlock, 40)
		local M11 = buffer.readu32(MessageBlock, 44)
		local M12 = buffer.readu32(MessageBlock, 48)
		local M13 = buffer.readu32(MessageBlock, 52)
		local M14 = buffer.readu32(MessageBlock, 56)
		local M15 = buffer.readu32(MessageBlock, 60)

		local XOR = bit32.bxor
		local LEFTROTATE = bit32.lrotate

		local Temp
		for Index = 1, 7 do
			V00 += V04 + M00
			V12 = LEFTROTATE(XOR(V12, V00), 16)
			V08 += V12
			V04 = LEFTROTATE(XOR(V04, V08), 20)
			V00 += V04 + M01
			V12 = LEFTROTATE(XOR(V12, V00), 24)
			V08 += V12
			V04 = LEFTROTATE(XOR(V04, V08), 25)

			V01 += V05 + M02
			V13 = LEFTROTATE(XOR(V13, V01), 16)
			V09 += V13
			V05 = LEFTROTATE(XOR(V05, V09), 20)
			V01 += V05 + M03
			V13 = LEFTROTATE(XOR(V13, V01), 24)
			V09 += V13
			V05 = LEFTROTATE(XOR(V05, V09), 25)

			V02 += V06 + M04
			V14 = LEFTROTATE(XOR(V14, V02), 16)
			V10 += V14
			V06 = LEFTROTATE(XOR(V06, V10), 20)
			V02 += V06 + M05
			V14 = LEFTROTATE(XOR(V14, V02), 24)
			V10 += V14
			V06 = LEFTROTATE(XOR(V06, V10), 25)

			V03 += V07 + M06
			V15 = LEFTROTATE(XOR(V15, V03), 16)
			V11 += V15
			V07 = LEFTROTATE(XOR(V07, V11), 20)
			V03 += V07 + M07
			V15 = LEFTROTATE(XOR(V15, V03), 24)
			V11 += V15
			V07 = LEFTROTATE(XOR(V07, V11), 25)

			V00 += V05 + M08
			V15 = LEFTROTATE(XOR(V15, V00), 16)
			V10 += V15
			V05 = LEFTROTATE(XOR(V05, V10), 20)
			V00 += V05 + M09
			V15 = LEFTROTATE(XOR(V15, V00), 24)
			V10 += V15
			V05 = LEFTROTATE(XOR(V05, V10), 25)

			V01 += V06 + M10
			V12 = LEFTROTATE(XOR(V12, V01), 16)
			V11 += V12
			V06 = LEFTROTATE(XOR(V06, V11), 20)
			V01 += V06 + M11
			V12 = LEFTROTATE(XOR(V12, V01), 24)
			V11 += V12
			V06 = LEFTROTATE(XOR(V06, V11), 25)

			V02 += V07 + M12
			V13 = LEFTROTATE(XOR(V13, V02), 16)
			V08 += V13
			V07 = LEFTROTATE(XOR(V07, V08), 20)
			V02 += V07 + M13
			V13 = LEFTROTATE(XOR(V13, V02), 24)
			V08 += V13
			V07 = LEFTROTATE(XOR(V07, V08), 25)

			V03 += V04 + M14
			V14 = LEFTROTATE(XOR(V14, V03), 16)
			V09 += V14
			V04 = LEFTROTATE(XOR(V04, V09), 20)
			V03 += V04 + M15
			V14 = LEFTROTATE(XOR(V14, V03), 24)
			V09 += V14
			V04 = LEFTROTATE(XOR(V04, V09), 25)

			if Index ~= 7 then
				Temp = M02
				M02 = M03
				M03 = M10
				M10 = M12
				M12 = M09
				M09 = M11
				M11 = M05
				M05 = M00
				M00 = Temp

				Temp = M06
				M06 = M04
				M04 = M07
				M07 = M13
				M13 = M14
				M14 = M15
				M15 = M08
				M08 = M01
				M01 = Temp
			end
		end

		if IsFull then
			local Result = buffer.create(EXTENDED_CV_SIZE)
			buffer.writeu32(Result, 0, XOR(V00, V08))
			buffer.writeu32(Result, 4, XOR(V01, V09))
			buffer.writeu32(Result, 8, XOR(V02, V10))
			buffer.writeu32(Result, 12, XOR(V03, V11))
			buffer.writeu32(Result, 16, XOR(V04, V12))
			buffer.writeu32(Result, 20, XOR(V05, V13))
			buffer.writeu32(Result, 24, XOR(V06, V14))
			buffer.writeu32(Result, 28, XOR(V07, V15))

			buffer.writeu32(Result, 32, XOR(V08, Hash00))
			buffer.writeu32(Result, 36, XOR(V09, Hash01))
			buffer.writeu32(Result, 40, XOR(V10, Hash02))
			buffer.writeu32(Result, 44, XOR(V11, Hash03))
			buffer.writeu32(Result, 48, XOR(V12, Hash04))
			buffer.writeu32(Result, 52, XOR(V13, Hash05))
			buffer.writeu32(Result, 56, XOR(V14, Hash06))
			buffer.writeu32(Result, 60, XOR(V15, Hash07))

			return Result
		else
			local Result = buffer.create(CV_SIZE)
			buffer.writeu32(Result, 0, XOR(V00, V08))
			buffer.writeu32(Result, 4, XOR(V01, V09))
			buffer.writeu32(Result, 8, XOR(V02, V10))
			buffer.writeu32(Result, 12, XOR(V03, V11))
			buffer.writeu32(Result, 16, XOR(V04, V12))
			buffer.writeu32(Result, 20, XOR(V05, V13))
			buffer.writeu32(Result, 24, XOR(V06, V14))
			buffer.writeu32(Result, 28, XOR(V07, V15))

			return Result
		end
	end

	local function ProcessMessage(InitialHashVector: buffer, Flags: number, Message: buffer, Length: number): buffer
		local MessageLength = buffer.len(Message)
		local StateCvs = buffer.create(STACK_BUFFER_SIZE)
		local StackSize = 0
		local StateCv = buffer.create(CV_SIZE)
		buffer.copy(StateCv, 0, InitialHashVector, 0, CV_SIZE)

		local StateCounter = 0
		local StateChunkNumber = 0
		local StateEndFlag = 0
		local StateStartFlag = CHUNK_START

		local BlockBuffer = buffer.create(BLOCK_SIZE)

		for BlockOffset = 0, MessageLength - BLOCK_SIZE - 1, BLOCK_SIZE do
			buffer.copy(BlockBuffer, 0, Message, BlockOffset, BLOCK_SIZE)
			local StateFlags = Flags + StateStartFlag + StateEndFlag

			StateCv = Compress(StateCv, BlockBuffer, StateCounter, BLOCK_SIZE, StateFlags)
			StateStartFlag = 0
			StateChunkNumber += 1

			if StateChunkNumber == 15 then
				StateEndFlag = CHUNK_END
			elseif StateChunkNumber == 16 then
				local MergeCv = StateCv
				local MergeAmount = StateCounter + 1

				while MergeAmount % 2 == 0 do
					StackSize = StackSize - 1
					local PopCv = buffer.create(CV_SIZE)
					buffer.copy(PopCv, 0, StateCvs, StackSize * CV_SIZE, CV_SIZE)

					local Block = buffer.create(EXTENDED_CV_SIZE)
					buffer.copy(Block, 0, PopCv, 0, CV_SIZE)
					buffer.copy(Block, CV_SIZE, MergeCv, 0, CV_SIZE)

					MergeCv = Compress(InitialHashVector, Block, 0, BLOCK_SIZE, Flags + PARENT_FLAG)
					MergeAmount = MergeAmount / 2
				end

				buffer.copy(StateCvs, StackSize * CV_SIZE, MergeCv, 0, CV_SIZE)
				StackSize = StackSize + 1
				buffer.copy(StateCv, 0, InitialHashVector, 0, CV_SIZE)
				StateStartFlag = CHUNK_START

				StateCounter += 1
				StateChunkNumber = 0
				StateEndFlag = 0
			end
		end

		local LastLength = MessageLength == 0 and 0 or ((MessageLength - 1) % BLOCK_SIZE + 1)
		local PaddedMessage = buffer.create(BLOCK_SIZE)

		if LastLength > 0 then
			buffer.copy(PaddedMessage, 0, Message, MessageLength - LastLength, LastLength)
		end

		local OutputCv: buffer
		local OutputBlock: buffer
		local OutputLength: number
		local OutputFlags: number

		if StateCounter > 0 then
			local StateFlags = Flags + StateStartFlag + CHUNK_END
			local MergeCv = Compress(StateCv, PaddedMessage, StateCounter, LastLength, StateFlags)

			for Index = StackSize, 2, -1 do
				local StackCv = buffer.create(CV_SIZE)
				buffer.copy(StackCv, 0, StateCvs, (Index - 1) * CV_SIZE, CV_SIZE)

				local Block = buffer.create(EXTENDED_CV_SIZE)
				buffer.copy(Block, 0, StackCv, 0, CV_SIZE)
				buffer.copy(Block, CV_SIZE, MergeCv, 0, CV_SIZE)

				MergeCv = Compress(InitialHashVector, Block, 0, BLOCK_SIZE, Flags + PARENT_FLAG)
			end

			OutputCv = InitialHashVector
			local FirstStackCv = buffer.create(CV_SIZE)
			buffer.copy(FirstStackCv, 0, StateCvs, 0, CV_SIZE)

			OutputBlock = buffer.create(EXTENDED_CV_SIZE)
			buffer.copy(OutputBlock, 0, FirstStackCv, 0, CV_SIZE)
			buffer.copy(OutputBlock, CV_SIZE, MergeCv, 0, CV_SIZE)

			OutputLength = BLOCK_SIZE
			OutputFlags = Flags + ROOT_FLAG + PARENT_FLAG
		else
			OutputCv = StateCv
			OutputBlock = PaddedMessage
			OutputLength = LastLength
			OutputFlags = Flags + StateStartFlag + CHUNK_END + ROOT_FLAG
		end

		local Output = buffer.create(Length)
		local OutputOffset = 0

		for Index = 0, Length // BLOCK_SIZE do
			local MessageDigest = Compress(OutputCv, OutputBlock, Index, OutputLength, OutputFlags, true)

			local BytesToCopy = math.min(BLOCK_SIZE, Length - OutputOffset)
			buffer.copy(Output, OutputOffset, MessageDigest, 0, BytesToCopy)
			OutputOffset += BytesToCopy

			if OutputOffset >= Length then
				break
			end
		end

		return Output
	end

	Funcs.Blake3 = function(Message: buffer, Length: number?): buffer
		return ProcessMessage(INITIAL_VECTORS, 0, Message, Length or 32)
	end
end

do
	--!strict
	--!native
	--!optimize 2

	local DWORD = 4
	local BLOCK_SIZE = 64
	local STATE_SIZE = 16

	local CHACHA20_NONCE_SIZE = 12
	local CHACHA20_KEY_SIZE_16 = 16
	local CHACHA20_KEY_SIZE_32 = 32

	local SIGMA_CONSTANTS = buffer.create(16)
	do
		local SigmaBytes = { string.byte("expand 32-byte k", 1, -1) }
		for Index, ByteValue in SigmaBytes do
			buffer.writeu8(SIGMA_CONSTANTS, Index - 1, ByteValue)
		end
	end

	local TAU_CONSTANTS = buffer.create(16)
	do
		local TauBytes = { string.byte("expand 16-byte k", 1, -1) }
		for Index, ByteValue in TauBytes do
			buffer.writeu8(TAU_CONSTANTS, Index - 1, ByteValue)
		end
	end

	local function ProcessBlock(InitialState: buffer, Rounds: number)
		local S0: number, S1: number, S2: number, S3: number, S4: number, S5: number, S6: number, S7: number, S8: number, S9: number, S10: number, S11: number, S12: number, S13: number, S14: number, S15: number =
			buffer.readu32(InitialState, 0),
			buffer.readu32(InitialState, 4),
			buffer.readu32(InitialState, 8),
			buffer.readu32(InitialState, 12),
			buffer.readu32(InitialState, 16),
			buffer.readu32(InitialState, 20),
			buffer.readu32(InitialState, 24),
			buffer.readu32(InitialState, 28),
			buffer.readu32(InitialState, 32),
			buffer.readu32(InitialState, 36),
			buffer.readu32(InitialState, 40),
			buffer.readu32(InitialState, 44),
			buffer.readu32(InitialState, 48),
			buffer.readu32(InitialState, 52),
			buffer.readu32(InitialState, 56),
			buffer.readu32(InitialState, 60)

		for Round = 1, Rounds do
			local IsOddRound = Round % 2 == 1

			if IsOddRound then
				S0 = bit32.bor(S0 + S4, 0)
				S12 = bit32.lrotate(bit32.bxor(S12, S0), 16)
				S8 = bit32.bor(S8 + S12, 0)
				S4 = bit32.lrotate(bit32.bxor(S4, S8), 12)
				S0 = bit32.bor(S0 + S4, 0)
				S12 = bit32.lrotate(bit32.bxor(S12, S0), 8)
				S8 = bit32.bor(S8 + S12, 0)
				S4 = bit32.lrotate(bit32.bxor(S4, S8), 7)

				S1 = bit32.bor(S1 + S5, 0)
				S13 = bit32.lrotate(bit32.bxor(S13, S1), 16)
				S9 = bit32.bor(S9 + S13, 0)
				S5 = bit32.lrotate(bit32.bxor(S5, S9), 12)
				S1 = bit32.bor(S1 + S5, 0)
				S13 = bit32.lrotate(bit32.bxor(S13, S1), 8)
				S9 = bit32.bor(S9 + S13, 0)
				S5 = bit32.lrotate(bit32.bxor(S5, S9), 7)

				S2 = bit32.bor(S2 + S6, 0)
				S14 = bit32.lrotate(bit32.bxor(S14, S2), 16)
				S10 = bit32.bor(S10 + S14, 0)
				S6 = bit32.lrotate(bit32.bxor(S6, S10), 12)
				S2 = bit32.bor(S2 + S6, 0)
				S14 = bit32.lrotate(bit32.bxor(S14, S2), 8)
				S10 = bit32.bor(S10 + S14, 0)
				S6 = bit32.lrotate(bit32.bxor(S6, S10), 7)

				S3 = bit32.bor(S3 + S7, 0)
				S15 = bit32.lrotate(bit32.bxor(S15, S3), 16)
				S11 = bit32.bor(S11 + S15, 0)
				S7 = bit32.lrotate(bit32.bxor(S7, S11), 12)
				S3 = bit32.bor(S3 + S7, 0)
				S15 = bit32.lrotate(bit32.bxor(S15, S3), 8)
				S11 = bit32.bor(S11 + S15, 0)
				S7 = bit32.lrotate(bit32.bxor(S7, S11), 7)
			else
				S0 = bit32.bor(S0 + S5, 0)
				S15 = bit32.lrotate(bit32.bxor(S15, S0), 16)
				S10 = bit32.bor(S10 + S15, 0)
				S5 = bit32.lrotate(bit32.bxor(S5, S10), 12)
				S0 = bit32.bor(S0 + S5, 0)
				S15 = bit32.lrotate(bit32.bxor(S15, S0), 8)
				S10 = bit32.bor(S10 + S15, 0)
				S5 = bit32.lrotate(bit32.bxor(S5, S10), 7)

				S1 = bit32.bor(S1 + S6, 0)
				S12 = bit32.lrotate(bit32.bxor(S12, S1), 16)
				S11 = bit32.bor(S11 + S12, 0)
				S6 = bit32.lrotate(bit32.bxor(S6, S11), 12)
				S1 = bit32.bor(S1 + S6, 0)
				S12 = bit32.lrotate(bit32.bxor(S12, S1), 8)
				S11 = bit32.bor(S11 + S12, 0)
				S6 = bit32.lrotate(bit32.bxor(S6, S11), 7)

				S2 = bit32.bor(S2 + S7, 0)
				S13 = bit32.lrotate(bit32.bxor(S13, S2), 16)
				S8 = bit32.bor(S8 + S13, 0)
				S7 = bit32.lrotate(bit32.bxor(S7, S8), 12)
				S2 = bit32.bor(S2 + S7, 0)
				S13 = bit32.lrotate(bit32.bxor(S13, S2), 8)
				S8 = bit32.bor(S8 + S13, 0)
				S7 = bit32.lrotate(bit32.bxor(S7, S8), 7)

				S3 = bit32.bor(S3 + S4, 0)
				S14 = bit32.lrotate(bit32.bxor(S14, S3), 16)
				S9 = bit32.bor(S9 + S14, 0)
				S4 = bit32.lrotate(bit32.bxor(S4, S9), 12)
				S3 = bit32.bor(S3 + S4, 0)
				S14 = bit32.lrotate(bit32.bxor(S14, S3), 8)
				S9 = bit32.bor(S9 + S14, 0)
				S4 = bit32.lrotate(bit32.bxor(S4, S9), 7)
			end
		end

		buffer.writeu32(InitialState, 0, buffer.readu32(InitialState, 0) + S0)
		buffer.writeu32(InitialState, 4, buffer.readu32(InitialState, 4) + S1)
		buffer.writeu32(InitialState, 8, buffer.readu32(InitialState, 8) + S2)
		buffer.writeu32(InitialState, 12, buffer.readu32(InitialState, 12) + S3)
		buffer.writeu32(InitialState, 16, buffer.readu32(InitialState, 16) + S4)
		buffer.writeu32(InitialState, 20, buffer.readu32(InitialState, 20) + S5)
		buffer.writeu32(InitialState, 24, buffer.readu32(InitialState, 24) + S6)
		buffer.writeu32(InitialState, 28, buffer.readu32(InitialState, 28) + S7)
		buffer.writeu32(InitialState, 32, buffer.readu32(InitialState, 32) + S8)
		buffer.writeu32(InitialState, 36, buffer.readu32(InitialState, 36) + S9)
		buffer.writeu32(InitialState, 40, buffer.readu32(InitialState, 40) + S10)
		buffer.writeu32(InitialState, 44, buffer.readu32(InitialState, 44) + S11)
		buffer.writeu32(InitialState, 48, buffer.readu32(InitialState, 48) + S12)
		buffer.writeu32(InitialState, 52, buffer.readu32(InitialState, 52) + S13)
		buffer.writeu32(InitialState, 56, buffer.readu32(InitialState, 56) + S14)
		buffer.writeu32(InitialState, 60, buffer.readu32(InitialState, 60) + S15)
	end

	local function InitializeState(Key: buffer, Nonce: buffer, Counter: number): buffer
		local KeyLength = buffer.len(Key)
		local State = buffer.create(STATE_SIZE * DWORD)

		local Constants = KeyLength == 32 and SIGMA_CONSTANTS or TAU_CONSTANTS

		buffer.copy(State, 0, Constants, 0, 16)

		buffer.copy(State, 16, Key, 0, math.min(KeyLength, 16))
		if KeyLength == 32 then
			buffer.copy(State, 32, Key, 16, 16)
		else
			buffer.copy(State, 32, Key, 0, 16)
		end

		buffer.writeu32(State, 48, Counter)
		buffer.copy(State, 52, Nonce, 0, 12)

		return State
	end

	Funcs.ChaCha20 = function(Data: buffer, Key: buffer, Nonce: buffer, Counter: number?, Rounds: number?): buffer
		if Data == nil then
			error("Data cannot be nil", 2)
		end

		if typeof(Data) ~= "buffer" then
			error(`Data must be a buffer, got {typeof(Data)}`, 2)
		end

		if Key == nil then
			error("Key cannot be nil", 2)
		end

		if typeof(Key) ~= "buffer" then
			error(`Key must be a buffer, got {typeof(Key)}`, 2)
		end

		local KeyLength = buffer.len(Key)
		if KeyLength ~= CHACHA20_KEY_SIZE_16 and KeyLength ~= CHACHA20_KEY_SIZE_32 then
			error(`Key must be {CHACHA20_KEY_SIZE_16} or {CHACHA20_KEY_SIZE_32} bytes long, got {KeyLength} bytes`, 2)
		end

		if Nonce == nil then
			error("Nonce cannot be nil", 2)
		end

		if typeof(Nonce) ~= "buffer" then
			error(`Nonce must be a buffer, got {typeof(Nonce)}`, 2)
		end

		local NonceLength = buffer.len(Nonce)
		if NonceLength ~= CHACHA20_NONCE_SIZE then
			error(`Nonce must be exactly {CHACHA20_NONCE_SIZE} bytes long, got {NonceLength} bytes`, 2)
		end

		if Counter then
			if typeof(Counter) ~= "number" then
				error(`Counter must be a number, got {typeof(Counter)}`, 2)
			end

			if Counter < 0 then
				error(`Counter cannot be negative, got {Counter}`, 2)
			end

			if Counter ~= math.floor(Counter) then
				error(`Counter must be an integer, got {Counter}`, 2)
			end

			if Counter >= 2 ^ 32 then
				error(`Counter must be less than 2^32, got {Counter}`, 2)
			end
		end

		if Rounds then
			if typeof(Rounds) ~= "number" then
				error(`Rounds must be a number, got {typeof(Rounds)}`, 2)
			end

			if Rounds <= 0 then
				error(`Rounds must be positive, got {Rounds}`, 2)
			end

			if Rounds ~= math.floor(Rounds) then
				error(`Rounds must be an integer, got {Rounds}`, 2)
			end

			if Rounds % 2 ~= 0 then
				error(`Rounds must be even, got {Rounds}`, 2)
			end
		end

		local BlockCounter = Counter or 1
		local BlockRounds = Rounds or 20

		local DataLength = buffer.len(Data)
		if DataLength == 0 then
			return buffer.create(0)
		end

		local Output = buffer.create(DataLength)

		local DataOffset = 0

		local State = InitializeState(Key, Nonce, BlockCounter)
		local StateBackup = buffer.create(64)
		buffer.copy(StateBackup, 0, State, 0)

		while DataOffset < DataLength do
			ProcessBlock(State, BlockRounds)

			local BytesToProcess = math.min(BLOCK_SIZE, DataLength - DataOffset)

			for Index = 0, BytesToProcess - 1 do
				local DataByte = buffer.readu8(Data, DataOffset + Index)
				local KeystreamByte = buffer.readu8(State, Index)
				buffer.writeu8(Output, DataOffset + Index, bit32.bxor(DataByte, KeystreamByte))
			end

			DataOffset += BytesToProcess
			BlockCounter += 1
			buffer.copy(State, 0, StateBackup, 0)
			buffer.writeu32(State, 48, BlockCounter)
		end

		return Output
	end
end

do
	--!strict
	--!optimize 2
	--!native

	local ENCODE_LOOKUP = buffer.create(256 * 2)
	do
		local HexChars = "0123456789abcdef"
		for Byte = 0, 255 do
			local HighNibble = bit32.rshift(Byte, 4)
			local LowNibble = Byte % 16

			local HighChar = string.byte(HexChars, HighNibble + 1)
			local LowChar = string.byte(HexChars, LowNibble + 1)

			local Combined = HighChar + bit32.lshift(LowChar, 8)
			buffer.writeu16(ENCODE_LOOKUP, Byte * 2, Combined)
		end
	end

	local DECODE_LOOKUP = buffer.create(65536 * 2)
	do
		for High = 0, 255 do
			for Low = 0, 255 do
				local HighNibble = 0
				local LowNibble = 0

				if High >= 48 and High <= 57 then
					HighNibble = High - 48
				elseif High >= 65 and High <= 70 then
					HighNibble = High - 55
				elseif High >= 97 and High <= 102 then
					HighNibble = High - 87
				else
					HighNibble = 0
				end

				if Low >= 48 and Low <= 57 then
					LowNibble = Low - 48
				elseif Low >= 65 and Low <= 70 then
					LowNibble = Low - 55
				elseif Low >= 97 and Low <= 102 then
					LowNibble = Low - 87
				else
					LowNibble = 0
				end

				local Combined = bit32.lshift(HighNibble, 4) + LowNibble
				local Index = bit32.lshift(Low, 8) + High
				buffer.writeu16(DECODE_LOOKUP, Index * 2, Combined)
			end
		end
	end

	local Conversions = {}

	function Conversions.ToHex(Buffer: buffer): string
		local Length = buffer.len(Buffer)
		local Hex = buffer.create(Length * 2)

		local Lookup = ENCODE_LOOKUP

		local Leftover = Length % 8
		local HexCursor = 0

		for Index = 0, Length - Leftover - 1, 8 do
			local Hex1 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index) * 2)
			local Hex2 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 1) * 2)
			local Hex3 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 2) * 2)
			local Hex4 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 3) * 2)
			local Hex5 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 4) * 2)
			local Hex6 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 5) * 2)
			local Hex7 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 6) * 2)
			local Hex8 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 7) * 2)

			buffer.writeu16(Hex, HexCursor, Hex1)
			buffer.writeu16(Hex, HexCursor + 2, Hex2)
			buffer.writeu16(Hex, HexCursor + 4, Hex3)
			buffer.writeu16(Hex, HexCursor + 6, Hex4)
			buffer.writeu16(Hex, HexCursor + 8, Hex5)
			buffer.writeu16(Hex, HexCursor + 10, Hex6)
			buffer.writeu16(Hex, HexCursor + 12, Hex7)
			buffer.writeu16(Hex, HexCursor + 14, Hex8)

			HexCursor += 16
		end

		for Index = Length - Leftover, Length - 1 do
			local HexPair = buffer.readu16(Lookup, buffer.readu8(Buffer, Index) * 2)
			buffer.writeu16(Hex, HexCursor, HexPair)
			HexCursor += 2
		end

		return buffer.tostring(Hex)
	end

	function Conversions.FromHex(Hex: string | buffer): buffer
		local BufferHex = if type(Hex) == "string" then buffer.fromstring(Hex) else Hex
		local Length = buffer.len(BufferHex)
		if Length % 2 ~= 0 then
			error(`Length must be even, got {Length}`)
		end

		local Buffer = buffer.create(bit32.rshift(Length, 1))
		local Leftover = Length % 16
		local BufferCursor = 0
		local Lookup = DECODE_LOOKUP

		for Index = 0, Length - Leftover - 1, 16 do
			local Pair1 = buffer.readu16(BufferHex, Index)
			local Pair2 = buffer.readu16(BufferHex, Index + 2)
			local Pair3 = buffer.readu16(BufferHex, Index + 4)
			local Pair4 = buffer.readu16(BufferHex, Index + 6)
			local Pair5 = buffer.readu16(BufferHex, Index + 8)
			local Pair6 = buffer.readu16(BufferHex, Index + 10)
			local Pair7 = buffer.readu16(BufferHex, Index + 12)
			local Pair8 = buffer.readu16(BufferHex, Index + 14)

			local Byte1 = buffer.readu16(Lookup, Pair1 * 2)
			local Byte2 = buffer.readu16(Lookup, Pair2 * 2)
			local Byte3 = buffer.readu16(Lookup, Pair3 * 2)
			local Byte4 = buffer.readu16(Lookup, Pair4 * 2)
			local Byte5 = buffer.readu16(Lookup, Pair5 * 2)
			local Byte6 = buffer.readu16(Lookup, Pair6 * 2)
			local Byte7 = buffer.readu16(Lookup, Pair7 * 2)
			local Byte8 = buffer.readu16(Lookup, Pair8 * 2)

			local Chunk1 = bit32.lshift(Byte4, 24) + bit32.lshift(Byte3, 16) + bit32.lshift(Byte2, 8) + Byte1
			local Chunk2 = bit32.lshift(Byte8, 24) + bit32.lshift(Byte7, 16) + bit32.lshift(Byte6, 8) + Byte5

			buffer.writeu32(Buffer, BufferCursor, Chunk1)
			buffer.writeu32(Buffer, BufferCursor + 4, Chunk2)
			BufferCursor += 8
		end

		for Index = Length - Leftover, Length - 1, 2 do
			local Pair = buffer.readu16(BufferHex, Index)
			local Byte = buffer.readu16(Lookup, Pair * 2)
			buffer.writeu8(Buffer, BufferCursor, Byte)
			BufferCursor += 1
		end

		return Buffer
	end

	Utils.Conversions = Conversions
end

do
	--!strict
	--!optimize 2
	--!native

	export type EntropyProvider = (BytesLeft: number) -> buffer?

	local BLOCK_SIZE = 64
	local KEY_SIZE = 32
	local NONCE_SIZE = 12

	local CSPRNG: CSPRNGModule = {
		BlockExpansion = true,
		SizeTarget = 2048,
		RekeyAfter = 1024,

		Key = buffer.create(0),
		Nonce = buffer.create(0),
		Buffer = buffer.create(0),

		Counter = 0,
		BufferPosition = 0,
		BufferSize = 0,
		BytesLeft = 0,

		EntropyProviders = {},
	} :: CSPRNGModule

	local INPUT_BUFFER = buffer.create(BLOCK_SIZE)
	local REKEY_THRESHOLD = math.max(math.floor(CSPRNG.RekeyAfter), 2)
	local SIZE_TARGET_CLAMPED = math.clamp(math.floor(CSPRNG.SizeTarget), 64, 4294967295)

	local function Reset()
		CSPRNG.Key = buffer.create(0)
		CSPRNG.Nonce = buffer.create(0)
		CSPRNG.Buffer = buffer.create(0)

		CSPRNG.Counter = 0
		CSPRNG.BufferPosition = 0
		CSPRNG.BufferSize = 0
	end

	local function GatherEntropy(CustomEntropy: buffer?): number
		local EntropyBuffers = buffer.create(1024)
		local Offset = 0

		local function WriteToBuffer(Source: buffer)
			local Size = buffer.len(Source)
			buffer.copy(EntropyBuffers, Offset, Source, 0, Size)
			Offset += Size
		end

		local CurrentTime = 1.234
		if tick then
			CurrentTime = tick()
			local TimeBuffer = buffer.create(8)
			buffer.writef64(TimeBuffer, 0, CurrentTime)
			WriteToBuffer(TimeBuffer)
		end

		local ClockTime = os.clock()
		local ClockBuffer = buffer.create(8)
		buffer.writef64(ClockBuffer, 0, ClockTime)
		WriteToBuffer(ClockBuffer)

		local UnixTime = os.time()
		local UnixBuffer = buffer.create(8)
		buffer.writeu32(UnixBuffer, 0, UnixTime % 0x100000000)
		buffer.writeu32(UnixBuffer, 4, math.floor(UnixTime / 0x100000000))
		WriteToBuffer(UnixBuffer)

		local DateTimeMillis = 5.678
		if DateTime then
			DateTimeMillis = DateTime.now().UnixTimestampMillis
			local DateTimeBuffer = buffer.create(8)
			buffer.writef64(DateTimeBuffer, 0, DateTimeMillis)
			WriteToBuffer(DateTimeBuffer)

			local DateTimePrecisionBuffer = buffer.create(16)
			buffer.writef32(DateTimePrecisionBuffer, 0, DateTimeMillis / 1000)
			buffer.writef32(DateTimePrecisionBuffer, 4, (DateTimeMillis % 1000) / 100)
			buffer.writef32(DateTimePrecisionBuffer, 8, DateTimeMillis / 86400000)
			buffer.writef32(DateTimePrecisionBuffer, 12, (DateTimeMillis * 0.001) % 1)
			WriteToBuffer(DateTimePrecisionBuffer)
		else
			WriteToBuffer(buffer.create(24))
		end

		local FracTimeBuffer = buffer.create(16)
		buffer.writef32(FracTimeBuffer, 0, ClockTime / 100)
		buffer.writef32(FracTimeBuffer, 4, CurrentTime / 1000)
		buffer.writef32(FracTimeBuffer, 8, (ClockTime * 12345.6789) % 1)
		buffer.writef32(FracTimeBuffer, 12, (CurrentTime * 98765.4321) % 1)
		WriteToBuffer(FracTimeBuffer)

		local NoiseBuffer = buffer.create(32)
		for Index = 0, 7 do
			local Noise1 = math.noise(ClockTime + Index, UnixTime + Index, ClockTime + UnixTime + Index)
			local Noise2 =
				math.noise(CurrentTime + Index * 0.1, DateTimeMillis * 0.0001 + Index, ClockTime * 1.5 + Index)
			local Noise3 =
				math.noise(UnixTime * 0.01 + Index, ClockTime + DateTimeMillis * 0.001, CurrentTime + Index * 2)
			local Noise4 =
				math.noise(DateTimeMillis * 0.00001 + Index, UnixTime + ClockTime + Index, CurrentTime * 0.1 + Index)

			buffer.writef32(NoiseBuffer, Index * 4, Noise1 + Noise2 + Noise3 + Noise4)
		end
		WriteToBuffer(NoiseBuffer)

		local BenchmarkTimings = buffer.create(32)
		for Index = 0, 7 do
			local StartTime = os.clock()
			local Sum = 0

			local Iterations = 50 + (Index * 25)
			for Iteration = 1, Iterations do
				Sum += Iteration * Iteration + math.sin(Iteration / 10) * math.cos(Iteration / 7)
			end

			local EndTime = os.clock()
			local TimingDelta = EndTime - StartTime
			buffer.writef32(BenchmarkTimings, Index * 4, TimingDelta * 1000000)
		end
		WriteToBuffer(BenchmarkTimings)

		local AllocTimings = buffer.create(24)
		for Index = 0, 5 do
			local AllocStart = os.clock()

			for AllocIndex = 1, 20 do
				local _TempBuf = buffer.create(64 + AllocIndex)
			end

			local AllocEnd = os.clock()
			buffer.writef32(AllocTimings, Index * 4, (AllocEnd - AllocStart) * 10000000)
		end
		WriteToBuffer(AllocTimings)

		local MicroTime = math.floor(CurrentTime * 1000000)
		local MicroTimeBuffer = buffer.create(8)
		buffer.writeu32(MicroTimeBuffer, 0, MicroTime % 0x100000000)
		buffer.writeu32(MicroTimeBuffer, 4, math.floor(MicroTime / 0x100000000))
		WriteToBuffer(MicroTimeBuffer)

		if game then
			if game.JobId and #game.JobId > 0 then
				local JobIdBuffer = buffer.fromstring(game.JobId)
				WriteToBuffer(JobIdBuffer)
			end

			if game.PlaceId then
				local PlaceIdBuffer = buffer.create(8)
				buffer.writeu32(PlaceIdBuffer, 0, game.PlaceId % 0x100000000)
				buffer.writeu32(PlaceIdBuffer, 4, math.floor(game.PlaceId / 0x100000000))
				WriteToBuffer(PlaceIdBuffer)
			end

			if workspace and workspace.DistributedGameTime then
				local DistTimeBuffer = buffer.create(8)
				buffer.writef64(DistTimeBuffer, 0, workspace.DistributedGameTime)
				WriteToBuffer(DistTimeBuffer)

				local DistMicroTime = math.floor(workspace.DistributedGameTime * 1000000)
				local DistMicroBuffer = buffer.create(8)
				buffer.writeu32(DistMicroBuffer, 0, DistMicroTime % 0x100000000)
				buffer.writeu32(DistMicroBuffer, 4, math.floor(DistMicroTime / 0x100000000))
				WriteToBuffer(DistMicroBuffer)
			end
		end

		local AddressEntropy = buffer.create(128)
		for Index = 0, 7 do
			local TempTable = {}
			local TempFunc = function() end
			local TempBuffer = buffer.create(0)
			local TempUserdata = newproxy()

			local TableAddr = string.gsub(tostring(TempTable), "table: ", "")
			local FuncAddr = string.gsub(tostring(TempFunc), "function: ", "")
			local BufferAddr = string.gsub(tostring(TempBuffer), "buffer: ", "")
			local UserdataAddr = string.gsub(tostring(TempUserdata), "userdata: ", "")

			local TableHash = 0
			local ThreadHash = 0
			local FuncHash = 0
			local BufferHash = 0
			local UserdataHash = 0

			for AddrIndex = 1, #TableAddr do
				TableHash = bit32.bxor(TableHash, string.byte(TableAddr, AddrIndex)) * 31
			end

			if coroutine then
				local ThreadAddr = string.gsub(tostring(coroutine.create(function() end)), "thread: ", "")
				for AddrIndex = 1, #ThreadAddr do
					ThreadHash = bit32.bxor(ThreadHash, string.byte(ThreadAddr, AddrIndex)) * 31
				end
			end

			for AddrIndex = 1, #FuncAddr do
				FuncHash = bit32.bxor(FuncHash, string.byte(FuncAddr, AddrIndex)) * 37
			end
			for AddrIndex = 1, #BufferAddr do
				BufferHash = bit32.bxor(BufferHash, string.byte(BufferAddr, AddrIndex)) * 41
			end
			for AddrIndex = 1, #UserdataAddr do
				UserdataHash = bit32.bxor(UserdataHash, string.byte(UserdataAddr, AddrIndex)) * 43
			end

			buffer.writeu32(AddressEntropy, Index * 16, TableHash)
			buffer.writeu32(AddressEntropy, Index * 16 + 4, ThreadHash)
			buffer.writeu32(AddressEntropy, Index * 16 + 8, FuncHash)
			buffer.writeu32(AddressEntropy, Index * 16 + 12, bit32.bxor(BufferHash, UserdataHash))
		end
		WriteToBuffer(AddressEntropy)

		local function AddExtraEntropy(Entropy: buffer?, Warn: boolean, Provider: string?)
			if not Entropy then
				return
			end

			local BytesLeft = 1024 - Offset

			if BytesLeft > 0 then
				local Extra = buffer.len(Entropy) - BytesLeft
				local Truncated = math.min(BytesLeft, buffer.len(Entropy))

				if Extra > 0 and Warn and Provider then
					warn(
						`CSPRNG: {Provider} returned {Extra} bytes more than available and was truncated to {Truncated} bytes`
					)
				end

				buffer.copy(EntropyBuffers, Offset, Entropy, 0, Truncated)
			end
		end

		for Index, Provider in CSPRNG.EntropyProviders do
			local BytesLeft = 1024 - Offset
			if BytesLeft > 0 then
				local Success: boolean, ExtraEntropy: buffer? = pcall(Provider, BytesLeft)
				if not Success then
					warn(`CSPRNG Provider errored with {ExtraEntropy}`)
				end

				AddExtraEntropy(ExtraEntropy, true, `Entropy Provider #{Index}`)
			end
		end

		if CustomEntropy then
			AddExtraEntropy(CustomEntropy, false)
		end

		local KeyMaterial = Funcs.Blake3(EntropyBuffers, KEY_SIZE + NONCE_SIZE)

		CSPRNG.Key = buffer.create(KEY_SIZE)
		buffer.copy(CSPRNG.Key, 0, KeyMaterial, 0, KEY_SIZE)

		CSPRNG.Nonce = buffer.create(NONCE_SIZE)
		buffer.copy(CSPRNG.Nonce, 0, KeyMaterial, KEY_SIZE, NONCE_SIZE)

		return buffer.len(EntropyBuffers) - Offset
	end

	local function GenerateBlock()
		buffer.fill(INPUT_BUFFER, 0, 0, BLOCK_SIZE)
		local ChaChaOutput = Funcs.ChaCha20(INPUT_BUFFER, CSPRNG.Key, CSPRNG.Nonce, CSPRNG.Counter, 20)

		CSPRNG.Buffer = if CSPRNG.BlockExpansion then Funcs.Blake3(ChaChaOutput, SIZE_TARGET_CLAMPED) else ChaChaOutput
		CSPRNG.BufferPosition = 0
		CSPRNG.BufferSize = buffer.len(CSPRNG.Buffer)
		CSPRNG.Counter += 1

		if CSPRNG.Counter % REKEY_THRESHOLD == 0 then
			GatherEntropy()
			CSPRNG.Counter = 0
		end
	end

	local function GetBytes(Count: number): buffer
		local Result = buffer.create(Count)
		local ResultPosition = 0

		while ResultPosition < Count do
			if CSPRNG.BufferPosition >= CSPRNG.BufferSize then
				GenerateBlock()
			end

			local BytesNeeded = Count - ResultPosition
			local BytesAvailable = CSPRNG.BufferSize - CSPRNG.BufferPosition
			local BytesToCopy = math.min(BytesNeeded, BytesAvailable)

			buffer.copy(Result, ResultPosition, CSPRNG.Buffer, CSPRNG.BufferPosition, BytesToCopy)
			ResultPosition += BytesToCopy
			CSPRNG.BufferPosition += BytesToCopy
		end

		return Result
	end

	local function GetFloat(): number
		if CSPRNG.BufferPosition + 8 > CSPRNG.BufferSize then
			GenerateBlock()
		end

		local Value1 = buffer.readu32(CSPRNG.Buffer, CSPRNG.BufferPosition)
		local Value2 = buffer.readu32(CSPRNG.Buffer, CSPRNG.BufferPosition + 4)
		CSPRNG.BufferPosition += 8

		local High = bit32.rshift(Value1, 5)
		local Low = bit32.rshift(Value2, 6)

		return (High * 67108864.0 + Low) / 9007199254740992.0
	end

	local function GetIntRange(Min: number, Max: number): number
		local Range = Max - Min + 1
		local MaxUInt32 = 0xFFFFFFFF
		local Limit = MaxUInt32 - (MaxUInt32 % Range)

		if CSPRNG.BufferPosition + 4 > CSPRNG.BufferSize then
			GenerateBlock()
		end

		local Value = buffer.readu32(CSPRNG.Buffer, CSPRNG.BufferPosition)
		CSPRNG.BufferPosition += 4

		if bit32.band(Range, Range - 1) == 0 then
			return Min + bit32.band(Value, Range - 1)
		else
			while Value > Limit do
				if CSPRNG.BufferPosition + 4 > CSPRNG.BufferSize then
					GenerateBlock()
				end
				Value = buffer.readu32(CSPRNG.Buffer, CSPRNG.BufferPosition)
				CSPRNG.BufferPosition += 4
			end

			return Min + (Value % Range)
		end
	end

	local function GetNumberRange(Min: number, Max: number): number
		if Min > Max then
			Min, Max = Max, Min
		end

		local Range = Max - Min
		if Range <= 0 then
			return Min
		end

		return Min + (GetFloat() * Range)
	end

	local function GetRandomString(Length: number, AsBuffer: boolean?): string | buffer
		local Characters = buffer.create(Length)

		for Index = 0, Length - 1 do
			buffer.writeu8(Characters, Index, GetIntRange(36, 122))
		end

		return if AsBuffer then Characters else buffer.tostring(Characters)
	end

	local function GetEd25519RandomBytes(): buffer
		local Output = buffer.create(32)

		for Index = 0, 31 do
			buffer.writeu8(Output, Index, GetIntRange(0, 255))
		end

		return Output
	end

	local function GetEd25519ClampedBytes(Input: buffer): buffer
		local Output = buffer.create(32)
		buffer.copy(Output, 0, Input, 0, 32)

		local FirstByte = buffer.readu8(Output, 0)
		FirstByte = bit32.band(FirstByte, 0xF8)
		buffer.writeu8(Output, 0, FirstByte)

		local LastByte = buffer.readu8(Output, 31)
		LastByte = bit32.band(LastByte, 0x7F)
		LastByte = bit32.bor(LastByte, 0x40)
		buffer.writeu8(Output, 31, LastByte)

		local HasVariation = false
		local FirstMiddleByte = buffer.readu8(Output, 1)
		for Index = 2, 30 do
			if buffer.readu8(Output, Index) ~= FirstMiddleByte then
				HasVariation = true
				break
			end
		end

		if not HasVariation then
			buffer.writeu8(Output, 15, bit32.bxor(FirstMiddleByte, 0x55))
		end

		return Output
	end

	function CSPRNG.AddEntropyProvider(ProviderFunction: EntropyProvider)
		table.insert(CSPRNG.EntropyProviders, ProviderFunction)
	end

	function CSPRNG.RemoveEntropyProvider(ProviderFunction: EntropyProvider)
		for Index = #CSPRNG.EntropyProviders, 1, -1 do
			if CSPRNG.EntropyProviders[Index] == ProviderFunction then
				table.remove(CSPRNG.EntropyProviders, Index)
				break
			end
		end
	end

	function CSPRNG.Random(): number
		return GetFloat()
	end

	function CSPRNG.RandomInt(Min: number, Max: number?): number
		if Max and type(Max) ~= "number" then
			error(`Max must be a number or nil, got {typeof(Max)}`, 2)
		end

		if type(Min) ~= "number" then
			error(`Min must be a number, got {typeof(Min)}`, 2)
		end

		if Max and Max < Min then
			error(`Max ({Max}) can't be less than Min ({Min})`, 2)
		end

		if Max and Max == Min then
			error(`Max ({Max}) can't be equal to Min ({Min})`, 2)
		end

		local ActualMax: number
		local ActualMin: number

		if Max == nil then
			ActualMax = Min
			ActualMin = 1
		else
			ActualMax = Max
			ActualMin = Min
		end

		return GetIntRange(ActualMin, ActualMax)
	end

	function CSPRNG.RandomNumber(Min: number, Max: number?): number
		if Max and type(Max) ~= "number" then
			error(`Max must be a number or nil, got {typeof(Max)}`, 2)
		end

		if type(Min) ~= "number" then
			error(`Min must be a number, got {typeof(Min)}`, 2)
		end

		if Max and Max < Min then
			error(`Max ({Max}) must be bigger than Min ({Min})`, 2)
		end

		if Max and Max == Min then
			error(`Max ({Max}) can't be equal to Min ({Min})`, 2)
		end

		local ActualMax: number
		local ActualMin: number

		if Max == nil then
			ActualMax = Min
			ActualMin = 0
		else
			ActualMax = Max
			ActualMin = Min
		end

		return GetNumberRange(ActualMin, ActualMax)
	end

	function CSPRNG.RandomBytes(Count: number): buffer
		if type(Count) ~= "number" then
			error(`Count must be a number, got {typeof(Count)}`, 2)
		end

		if Count <= 0 then
			error(`Count must be bigger than 0, got {Count}`, 2)
		end

		if Count % 1 ~= 0 then
			error("Count must be an integer", 2)
		end

		return GetBytes(Count)
	end

	function CSPRNG.RandomString(Length: number, AsBuffer: boolean?): string | buffer
		if type(Length) ~= "number" then
			error(`Length must be a number, got {typeof(Length)}`, 2)
		end

		if Length <= 0 then
			error(`Length must be bigger than 0, got {Length}`, 2)
		end

		if Length % 1 ~= 0 then
			error("Length must be an integer", 2)
		end

		if AsBuffer ~= nil and type(AsBuffer) ~= "boolean" then
			error(`AsBuffer must be a boolean or nil, got {typeof(AsBuffer)}`, 2)
		end

		return GetRandomString(Length, AsBuffer)
	end

	function CSPRNG.RandomHex(Length: number): string
		if type(Length) ~= "number" then
			error(`Length must be a number, got {typeof(Length)}`, 2)
		end

		if Length <= 0 then
			error(`Length must be bigger than 0, got {Length}`, 2)
		end

		if Length % 1 ~= 0 then
			error("Length must be an integer", 2)
		end

		if Length % 2 ~= 0 then
			error(`Length must be even, got {Length}`, 2)
		end

		return GetHexString(Length)
	end

	function CSPRNG.Ed25519ClampedBytes(Input: buffer): buffer
		if type(Input) ~= "buffer" then
			error(`Input must be a buffer, got {typeof(Input)}`, 2)
		end

		return GetEd25519ClampedBytes(Input)
	end

	function CSPRNG.Ed25519Random(): buffer
		return GetEd25519ClampedBytes(GetEd25519RandomBytes())
	end

	function CSPRNG.Reseed(CustomEntropy: buffer?)
		if CustomEntropy ~= nil and type(CustomEntropy) ~= "buffer" then
			error(`CustomEntropy must be a buffer or nil, got {typeof(CustomEntropy)}`, 2)
		end

		Reset()
		GatherEntropy(CustomEntropy)
	end

	CSPRNG.BytesLeft = GatherEntropy()
	GenerateBlock()

	Utils.CSPRNG = CSPRNG
end

do
	--!strict
	--!optimize 2
	--!native

	type Processor = (PlaintextBlock: buffer, PlaintextOffset: number, OutputBuffer: buffer, OutputOffset: number) -> ()

	local AES = {}

	local SBOX_16BIT = buffer.create(131072)
	local SMIX_TABLE0 = buffer.create(65536)
	local SMIX_TABLE1 = buffer.create(65536)

	local ALL_TABLES = buffer.create(32 * 16 * 16)
	local DOUBLES = buffer.create(128 * 16)

	local INVS_XOR_TABLE = buffer.create(65536)
	local INVMIX_TABLE0 = buffer.create(65536)
	local INVMIX_TABLE1 = buffer.create(65536)

	local KEY_CONFIGS = {
		[16] = { ExpandedLength = 176, MaterialLength = 128 },
		[24] = { ExpandedLength = 208, MaterialLength = 160 },
		[32] = { ExpandedLength = 240, MaterialLength = 192 },
	}

	local SUBSTITUTION_BOX, INVERSE_SUBSTITUTION_BOX = buffer.create(256), buffer.create(256)
	do
		local GaloisMultiply3, GaloisMultiply9, GaloisMultiply11 =
			buffer.create(256), buffer.create(256), buffer.create(256)
		local function GaloisFieldMultiply(FirstValue: number, SecondValue: number): number
			local Product = 0
			for _ = 0, 7 do
				if SecondValue % 2 == 1 then
					Product = bit32.bxor(Product, FirstValue)
				end
				FirstValue = FirstValue >= 128 and bit32.bxor(FirstValue * 2 % 256, 27) or FirstValue * 2 % 256
				SecondValue = math.floor(SecondValue / 2)
			end

			return Product
		end

		local PolynomialP = 1
		local PolynomialQ = 1
		buffer.writeu8(SUBSTITUTION_BOX, 0, 99)

		for _ = 1, 255 do
			PolynomialP = bit32.bxor(PolynomialP, PolynomialP * 2, PolynomialP < 128 and 0 or 27) % 256
			PolynomialQ = bit32.bxor(PolynomialQ, PolynomialQ * 2)
			PolynomialQ = bit32.bxor(PolynomialQ, PolynomialQ * 4)
			PolynomialQ = bit32.bxor(PolynomialQ, PolynomialQ * 16) % 256
			if PolynomialQ >= 128 then
				PolynomialQ = bit32.bxor(PolynomialQ, 9)
			end

			local TempValue = bit32.bxor(
				PolynomialQ,
				PolynomialQ % 128 * 2 + PolynomialQ / 128,
				PolynomialQ % 64 * 4 + PolynomialQ / 64,
				PolynomialQ % 32 * 8 + PolynomialQ / 32,
				PolynomialQ % 16 * 16 + PolynomialQ / 16,
				99
			)
			buffer.writeu8(SUBSTITUTION_BOX, PolynomialP, TempValue)
			buffer.writeu8(INVERSE_SUBSTITUTION_BOX, TempValue, PolynomialP)
			buffer.writeu8(GaloisMultiply3, PolynomialP, GaloisFieldMultiply(3, PolynomialP))
			buffer.writeu8(GaloisMultiply9, PolynomialP, GaloisFieldMultiply(9, PolynomialP))
			buffer.writeu8(GaloisMultiply11, PolynomialP, GaloisFieldMultiply(11, PolynomialP))
		end

		local TableIndex = 0
		for OuterIndex = 0, 255 do
			local PolynomialPOuter = buffer.readu8(SUBSTITUTION_BOX, OuterIndex)
			local PolynomialPBytes = PolynomialPOuter * 256
			local Galois2 = GaloisFieldMultiply(2, PolynomialPOuter)
			local Galois13 = GaloisFieldMultiply(13, OuterIndex)
			local Galois14 = GaloisFieldMultiply(14, OuterIndex)

			for InnerIndex = 0, 255 do
				local PolynomialQInner = buffer.readu8(SUBSTITUTION_BOX, InnerIndex)

				buffer.writeu16(SBOX_16BIT, TableIndex * 2, PolynomialPBytes + PolynomialQInner)
				buffer.writeu8(
					INVS_XOR_TABLE,
					TableIndex,
					buffer.readu8(INVERSE_SUBSTITUTION_BOX, bit32.bxor(OuterIndex, InnerIndex))
				)
				buffer.writeu8(
					SMIX_TABLE0,
					TableIndex,
					bit32.bxor(Galois2, buffer.readu8(GaloisMultiply3, PolynomialQInner))
				)
				buffer.writeu8(SMIX_TABLE1, TableIndex, bit32.bxor(PolynomialPOuter, PolynomialQInner))
				buffer.writeu8(
					INVMIX_TABLE0,
					TableIndex,
					bit32.bxor(Galois14, buffer.readu8(GaloisMultiply11, InnerIndex))
				)
				buffer.writeu8(
					INVMIX_TABLE1,
					TableIndex,
					bit32.bxor(Galois13, buffer.readu8(GaloisMultiply9, InnerIndex))
				)
				TableIndex += 1
			end
		end
	end

	local function ExpandKeySchedule(Key: buffer, KeyLength: number, OutputBuffer: buffer): buffer
		buffer.copy(OutputBuffer, 0, Key, 0, KeyLength)

		local Word = bit32.rrotate(buffer.readu32(OutputBuffer, KeyLength - 4), 8)
		local RoundConstant = 0.5
		local SBox_16 = SBOX_16BIT

		if KeyLength == 32 then
			for KeyOffset = 32, 192, 32 do
				RoundConstant = RoundConstant * 2 % 229
				local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536
					+ buffer.readu16(SBox_16, Word % 65536 * 2)
				Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 32), SBoxLookup, RoundConstant)
				buffer.writeu32(OutputBuffer, KeyOffset, Word)

				local W1 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 28), Word)
				buffer.writeu32(OutputBuffer, KeyOffset + 4, W1)
				local W2 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 24), W1)
				buffer.writeu32(OutputBuffer, KeyOffset + 8, W2)
				local W3 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 20), W2)
				buffer.writeu32(OutputBuffer, KeyOffset + 12, W3)

				SBoxLookup = buffer.readu16(SBox_16, W3 // 65536 * 2) * 65536 + buffer.readu16(SBox_16, W3 % 65536 * 2)
				Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 16), SBoxLookup)
				buffer.writeu32(OutputBuffer, KeyOffset + 16, Word)

				W1 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 12), Word)
				buffer.writeu32(OutputBuffer, KeyOffset + 20, W1)
				W2 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 8), W1)
				buffer.writeu32(OutputBuffer, KeyOffset + 24, W2)
				Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 4), W2)
				buffer.writeu32(OutputBuffer, KeyOffset + 28, Word)
				Word = bit32.rrotate(Word, 8)
			end

			local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536
				+ buffer.readu16(SBox_16, Word % 65536 * 2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, 192), SBoxLookup, 64)
			buffer.writeu32(OutputBuffer, 224, Word)

			local W1 = bit32.bxor(buffer.readu32(OutputBuffer, 196), Word)
			buffer.writeu32(OutputBuffer, 228, W1)
			local W2 = bit32.bxor(buffer.readu32(OutputBuffer, 200), W1)
			buffer.writeu32(OutputBuffer, 232, W2)
			buffer.writeu32(OutputBuffer, 236, bit32.bxor(buffer.readu32(OutputBuffer, 204), W2))
		elseif KeyLength == 24 then
			for KeyOffset = 24, 168, 24 do
				RoundConstant = RoundConstant * 2 % 229
				local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536
					+ buffer.readu16(SBox_16, Word % 65536 * 2)
				Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 24), SBoxLookup, RoundConstant)
				buffer.writeu32(OutputBuffer, KeyOffset, Word)

				local W1 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 20), Word)
				buffer.writeu32(OutputBuffer, KeyOffset + 4, W1)
				local W2 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 16), W1)
				buffer.writeu32(OutputBuffer, KeyOffset + 8, W2)
				local W3 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 12), W2)
				buffer.writeu32(OutputBuffer, KeyOffset + 12, W3)
				local W4 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 8), W3)
				buffer.writeu32(OutputBuffer, KeyOffset + 16, W4)
				Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 4), W4)
				buffer.writeu32(OutputBuffer, KeyOffset + 20, Word)
				Word = bit32.rrotate(Word, 8)
			end

			local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536
				+ buffer.readu16(SBox_16, Word % 65536 * 2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, 168), SBoxLookup, 128)
			buffer.writeu32(OutputBuffer, 192, Word)

			local W1 = bit32.bxor(buffer.readu32(OutputBuffer, 172), Word)
			buffer.writeu32(OutputBuffer, 196, W1)
			local W2 = bit32.bxor(buffer.readu32(OutputBuffer, 176), W1)
			buffer.writeu32(OutputBuffer, 200, W2)
			buffer.writeu32(OutputBuffer, 204, bit32.bxor(buffer.readu32(OutputBuffer, 180), W2))
		else
			for KeyOffset = 16, 144, 16 do
				RoundConstant = RoundConstant * 2 % 229
				local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536
					+ buffer.readu16(SBox_16, Word % 65536 * 2)
				Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 16), SBoxLookup, RoundConstant)
				buffer.writeu32(OutputBuffer, KeyOffset, Word)

				local W1 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 12), Word)
				buffer.writeu32(OutputBuffer, KeyOffset + 4, W1)
				local W2 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 8), W1)
				buffer.writeu32(OutputBuffer, KeyOffset + 8, W2)
				Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 4), W2)
				buffer.writeu32(OutputBuffer, KeyOffset + 12, Word)
				Word = bit32.rrotate(Word, 8)
			end

			local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536
				+ buffer.readu16(SBox_16, Word % 65536 * 2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, 144), SBoxLookup, 54)
			buffer.writeu32(OutputBuffer, 160, Word)

			local W1 = bit32.bxor(buffer.readu32(OutputBuffer, 148), Word)
			buffer.writeu32(OutputBuffer, 164, W1)
			local W2 = bit32.bxor(buffer.readu32(OutputBuffer, 152), W1)
			buffer.writeu32(OutputBuffer, 168, W2)
			buffer.writeu32(OutputBuffer, 172, bit32.bxor(buffer.readu32(OutputBuffer, 156), W2))
		end

		return OutputBuffer
	end

	local A0: number, A1: number, A2: number, A3: number, A4: number, A5: number, A6: number, A7: number, A8: number, A9: number, A10: number, A11: number, A12: number, A13: number, A14: number, A15: number
	local function EncryptBlock(
		RoundKeys: buffer,
		MaterialLength: number,
		Plaintext: buffer,
		PlaintextOffset: number,
		Output: buffer,
		OutputOffset: number
	)
		A0 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset), buffer.readu8(RoundKeys, 0))
		A1 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 1), buffer.readu8(RoundKeys, 1))
		A2 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 2), buffer.readu8(RoundKeys, 2))
		A3 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 3), buffer.readu8(RoundKeys, 3))
		A4 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 4), buffer.readu8(RoundKeys, 4))
		A5 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 5), buffer.readu8(RoundKeys, 5))
		A6 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 6), buffer.readu8(RoundKeys, 6))
		A7 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 7), buffer.readu8(RoundKeys, 7))
		A8 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 8), buffer.readu8(RoundKeys, 8))
		A9 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 9), buffer.readu8(RoundKeys, 9))
		A10 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 10), buffer.readu8(RoundKeys, 10))
		A11 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 11), buffer.readu8(RoundKeys, 11))
		A12 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 12), buffer.readu8(RoundKeys, 12))
		A13 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 13), buffer.readu8(RoundKeys, 13))
		A14 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 14), buffer.readu8(RoundKeys, 14))
		A15 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 15), buffer.readu8(RoundKeys, 15))

		local B0: number, B1: number, B2: number, B3: number, B4: number, B5: number, B6: number, B7: number, B8: number, B9: number, B10: number, B11: number, B12: number, B13: number, B14: number, B15: number =
			A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15

		local I0: number = B0 * 256 + B5
		local I1: number = B5 * 256 + B10
		local I2: number = B10 * 256 + B15
		local I3: number = B15 * 256 + B0
		local I4: number = B4 * 256 + B9
		local I5: number = B9 * 256 + B14
		local I6: number = B14 * 256 + B3
		local I7: number = B3 * 256 + B4
		local I8: number = B8 * 256 + B13
		local I9: number = B13 * 256 + B2
		local I10: number = B2 * 256 + B7
		local I11: number = B7 * 256 + B8
		local I12: number = B12 * 256 + B1
		local I13: number = B1 * 256 + B6
		local I14: number = B6 * 256 + B11
		local I15: number = B11 * 256 + B12

		local Tbl0, Tbl1 = SMIX_TABLE0, SMIX_TABLE1
		for RoundOffset = 16, MaterialLength, 16 do
			B0 = bit32.bxor(buffer.readu8(Tbl0, I0), buffer.readu8(Tbl1, I2), buffer.readu8(RoundKeys, RoundOffset))
			B1 = bit32.bxor(buffer.readu8(Tbl0, I1), buffer.readu8(Tbl1, I3), buffer.readu8(RoundKeys, RoundOffset + 1))
			B2 = bit32.bxor(buffer.readu8(Tbl0, I2), buffer.readu8(Tbl1, I0), buffer.readu8(RoundKeys, RoundOffset + 2))
			B3 = bit32.bxor(buffer.readu8(Tbl0, I3), buffer.readu8(Tbl1, I1), buffer.readu8(RoundKeys, RoundOffset + 3))
			B4 = bit32.bxor(buffer.readu8(Tbl0, I4), buffer.readu8(Tbl1, I6), buffer.readu8(RoundKeys, RoundOffset + 4))
			B5 = bit32.bxor(buffer.readu8(Tbl0, I5), buffer.readu8(Tbl1, I7), buffer.readu8(RoundKeys, RoundOffset + 5))
			B6 = bit32.bxor(buffer.readu8(Tbl0, I6), buffer.readu8(Tbl1, I4), buffer.readu8(RoundKeys, RoundOffset + 6))
			B7 = bit32.bxor(buffer.readu8(Tbl0, I7), buffer.readu8(Tbl1, I5), buffer.readu8(RoundKeys, RoundOffset + 7))
			B8 =
				bit32.bxor(buffer.readu8(Tbl0, I8), buffer.readu8(Tbl1, I10), buffer.readu8(RoundKeys, RoundOffset + 8))
			B9 =
				bit32.bxor(buffer.readu8(Tbl0, I9), buffer.readu8(Tbl1, I11), buffer.readu8(RoundKeys, RoundOffset + 9))
			B10 = bit32.bxor(
				buffer.readu8(Tbl0, I10),
				buffer.readu8(Tbl1, I8),
				buffer.readu8(RoundKeys, RoundOffset + 10)
			)
			B11 = bit32.bxor(
				buffer.readu8(Tbl0, I11),
				buffer.readu8(Tbl1, I9),
				buffer.readu8(RoundKeys, RoundOffset + 11)
			)
			B12 = bit32.bxor(
				buffer.readu8(Tbl0, I12),
				buffer.readu8(Tbl1, I14),
				buffer.readu8(RoundKeys, RoundOffset + 12)
			)
			B13 = bit32.bxor(
				buffer.readu8(Tbl0, I13),
				buffer.readu8(Tbl1, I15),
				buffer.readu8(RoundKeys, RoundOffset + 13)
			)
			B14 = bit32.bxor(
				buffer.readu8(Tbl0, I14),
				buffer.readu8(Tbl1, I12),
				buffer.readu8(RoundKeys, RoundOffset + 14)
			)
			B15 = bit32.bxor(
				buffer.readu8(Tbl0, I15),
				buffer.readu8(Tbl1, I13),
				buffer.readu8(RoundKeys, RoundOffset + 15)
			)

			I0, I1, I2, I3 = B0 * 256 + B5, B5 * 256 + B10, B10 * 256 + B15, B15 * 256 + B0
			I4, I5, I6, I7 = B4 * 256 + B9, B9 * 256 + B14, B14 * 256 + B3, B3 * 256 + B4
			I8, I9, I10, I11 = B8 * 256 + B13, B13 * 256 + B2, B2 * 256 + B7, B7 * 256 + B8
			I12, I13, I14, I15 = B12 * 256 + B1, B1 * 256 + B6, B6 * 256 + B11, B11 * 256 + B12
		end

		buffer.writeu32(
			Output,
			OutputOffset,
			bit32.bxor(
				buffer.readu16(
					SBOX_16BIT,
					bit32.bxor(
						buffer.readu8(Tbl0, I15),
						buffer.readu8(SMIX_TABLE1, I13),
						buffer.readu8(RoundKeys, MaterialLength + 31)
					)
							* 512
						+ bit32.bxor(
								buffer.readu8(Tbl0, I10),
								buffer.readu8(SMIX_TABLE1, I8),
								buffer.readu8(RoundKeys, MaterialLength + 26)
							)
							* 2
				)
						* 65536
					+ buffer.readu16(
						SBOX_16BIT,
						bit32.bxor(
							buffer.readu8(Tbl0, I5),
							buffer.readu8(SMIX_TABLE1, I7),
							buffer.readu8(RoundKeys, MaterialLength + 21)
						)
								* 512
							+ bit32.bxor(
									buffer.readu8(Tbl0, I0),
									buffer.readu8(SMIX_TABLE1, I2),
									buffer.readu8(RoundKeys, MaterialLength + 16)
								)
								* 2
					),
				buffer.readu32(RoundKeys, MaterialLength + 32)
			)
		)

		buffer.writeu32(
			Output,
			OutputOffset + 4,
			bit32.bxor(
				buffer.readu16(
					SBOX_16BIT,
					bit32.bxor(
						buffer.readu8(Tbl0, I3),
						buffer.readu8(SMIX_TABLE1, I1),
						buffer.readu8(RoundKeys, MaterialLength + 19)
					)
							* 512
						+ bit32.bxor(
								buffer.readu8(Tbl0, I14),
								buffer.readu8(SMIX_TABLE1, I12),
								buffer.readu8(RoundKeys, MaterialLength + 30)
							)
							* 2
				)
						* 65536
					+ buffer.readu16(
						SBOX_16BIT,
						bit32.bxor(
							buffer.readu8(Tbl0, I9),
							buffer.readu8(SMIX_TABLE1, I11),
							buffer.readu8(RoundKeys, MaterialLength + 25)
						)
								* 512
							+ bit32.bxor(
									buffer.readu8(Tbl0, I4),
									buffer.readu8(SMIX_TABLE1, I6),
									buffer.readu8(RoundKeys, MaterialLength + 20)
								)
								* 2
					),
				buffer.readu32(RoundKeys, MaterialLength + 36)
			)
		)

		buffer.writeu32(
			Output,
			OutputOffset + 8,
			bit32.bxor(
				buffer.readu16(
					SBOX_16BIT,
					bit32.bxor(
						buffer.readu8(Tbl0, I7),
						buffer.readu8(SMIX_TABLE1, I5),
						buffer.readu8(RoundKeys, MaterialLength + 23)
					)
							* 512
						+ bit32.bxor(
								buffer.readu8(Tbl0, I2),
								buffer.readu8(SMIX_TABLE1, I0),
								buffer.readu8(RoundKeys, MaterialLength + 18)
							)
							* 2
				)
						* 65536
					+ buffer.readu16(
						SBOX_16BIT,
						bit32.bxor(
							buffer.readu8(Tbl0, I13),
							buffer.readu8(SMIX_TABLE1, I15),
							buffer.readu8(RoundKeys, MaterialLength + 29)
						)
								* 512
							+ bit32.bxor(
									buffer.readu8(Tbl0, I8),
									buffer.readu8(SMIX_TABLE1, I10),
									buffer.readu8(RoundKeys, MaterialLength + 24)
								)
								* 2
					),
				buffer.readu32(RoundKeys, MaterialLength + 40)
			)
		)

		buffer.writeu32(
			Output,
			OutputOffset + 12,
			bit32.bxor(
				buffer.readu16(
					SBOX_16BIT,
					bit32.bxor(
						buffer.readu8(Tbl0, I11),
						buffer.readu8(SMIX_TABLE1, I9),
						buffer.readu8(RoundKeys, MaterialLength + 27)
					)
							* 512
						+ bit32.bxor(
								buffer.readu8(Tbl0, I6),
								buffer.readu8(SMIX_TABLE1, I4),
								buffer.readu8(RoundKeys, MaterialLength + 22)
							)
							* 2
				)
						* 65536
					+ buffer.readu16(
						SBOX_16BIT,
						bit32.bxor(
							buffer.readu8(Tbl0, I1),
							buffer.readu8(SMIX_TABLE1, I3),
							buffer.readu8(RoundKeys, MaterialLength + 17)
						)
								* 512
							+ bit32.bxor(
									buffer.readu8(Tbl0, I12),
									buffer.readu8(SMIX_TABLE1, I14),
									buffer.readu8(RoundKeys, MaterialLength + 28)
								)
								* 2
					),
				buffer.readu32(RoundKeys, MaterialLength + 44)
			)
		)
	end

	local function ConstantTimeCompare(Buffer1: buffer, Buffer2: buffer): boolean
		local Length1 = buffer.len(Buffer1)
		local Length2 = buffer.len(Buffer2)
		if Length1 ~= Length2 then
			return false
		end

		local Difference = 0
		for Index = 0, Length1 - 1 do
			Difference = bit32.bor(Difference, bit32.bxor(buffer.readu8(Buffer1, Index), buffer.readu8(Buffer2, Index)))
		end

		return Difference == 0
	end

	local function BuildShoupTables(H: buffer): buffer
		local Doubles = DOUBLES
		local AllTables = ALL_TABLES

		buffer.copy(Doubles, 0, H, 0, 16)

		for I = 1, 127 do
			local PrevOffset = (I - 1) * 16
			local CurrOffset = I * 16

			local LSB = bit32.band(buffer.readu8(Doubles, PrevOffset + 15), 1)

			local Carry = 0
			for BytePos = 0, 15 do
				local B = buffer.readu8(Doubles, PrevOffset + BytePos)
				local NewCarry = bit32.lshift(bit32.band(B, 1), 7)
				buffer.writeu8(Doubles, CurrOffset + BytePos, bit32.bor(bit32.rshift(B, 1), Carry))
				Carry = NewCarry
			end

			if LSB == 1 then
				buffer.writeu8(Doubles, CurrOffset, bit32.bxor(buffer.readu8(Doubles, CurrOffset), 0xE1))
			end
		end

		for NibbleIdx = 0, 31 do
			local TableOffset = NibbleIdx * 256

			buffer.writeu32(AllTables, TableOffset, 0)
			buffer.writeu32(AllTables, TableOffset + 4, 0)
			buffer.writeu32(AllTables, TableOffset + 8, 0)
			buffer.writeu32(AllTables, TableOffset + 12, 0)

			for Entry = 1, 15 do
				local EntryOffset = TableOffset + Entry * 16
				local Z0, Z1, Z2, Z3 = 0, 0, 0, 0

				for Bit = 0, 3 do
					if bit32.band(Entry, bit32.lshift(1, 3 - Bit)) ~= 0 then
						local DoubleOffset = (NibbleIdx * 4 + Bit) * 16

						Z0 = bit32.bxor(Z0, buffer.readu32(Doubles, DoubleOffset))
						Z1 = bit32.bxor(Z1, buffer.readu32(Doubles, DoubleOffset + 4))
						Z2 = bit32.bxor(Z2, buffer.readu32(Doubles, DoubleOffset + 8))
						Z3 = bit32.bxor(Z3, buffer.readu32(Doubles, DoubleOffset + 12))
					end
				end

				buffer.writeu32(AllTables, EntryOffset, Z0)
				buffer.writeu32(AllTables, EntryOffset + 4, Z1)
				buffer.writeu32(AllTables, EntryOffset + 8, Z2)
				buffer.writeu32(AllTables, EntryOffset + 12, Z3)
			end
		end

		return AllTables
	end

	local function GfMult(Y: buffer, Tables: buffer, Z: buffer)
		local Z0, Z1, Z2, Z3 = 0, 0, 0, 0

		for ByteIdx = 0, 15 do
			local ByteVal = buffer.readu8(Y, ByteIdx)
			local BaseOffset = ByteIdx * 512

			local HighOffset = BaseOffset + bit32.rshift(ByteVal, 4) * 16
			Z0 = bit32.bxor(Z0, buffer.readu32(Tables, HighOffset))
			Z1 = bit32.bxor(Z1, buffer.readu32(Tables, HighOffset + 4))
			Z2 = bit32.bxor(Z2, buffer.readu32(Tables, HighOffset + 8))
			Z3 = bit32.bxor(Z3, buffer.readu32(Tables, HighOffset + 12))

			local LowOffset = BaseOffset + 256 + bit32.band(ByteVal, 0x0F) * 16
			Z0 = bit32.bxor(Z0, buffer.readu32(Tables, LowOffset))
			Z1 = bit32.bxor(Z1, buffer.readu32(Tables, LowOffset + 4))
			Z2 = bit32.bxor(Z2, buffer.readu32(Tables, LowOffset + 8))
			Z3 = bit32.bxor(Z3, buffer.readu32(Tables, LowOffset + 12))
		end

		buffer.writeu32(Z, 0, Z0)
		buffer.writeu32(Z, 4, Z1)
		buffer.writeu32(Z, 8, Z2)
		buffer.writeu32(Z, 12, Z3)
	end

	local function Ghash(Tables: buffer, X: buffer, XLen: number, Y: buffer)
		local M = math.floor(XLen / 16)
		local XPos = 0
		local Tmp = buffer.create(16)
		local GfMult = GfMult

		for _ = 1, M do
			buffer.writeu32(Y, 0, bit32.bxor(buffer.readu32(Y, 0), buffer.readu32(X, XPos)))
			buffer.writeu32(Y, 4, bit32.bxor(buffer.readu32(Y, 4), buffer.readu32(X, XPos + 4)))
			buffer.writeu32(Y, 8, bit32.bxor(buffer.readu32(Y, 8), buffer.readu32(X, XPos + 8)))
			buffer.writeu32(Y, 12, bit32.bxor(buffer.readu32(Y, 12), buffer.readu32(X, XPos + 12)))
			XPos += 16

			GfMult(Y, Tables, Tmp)

			buffer.writeu32(Y, 0, buffer.readu32(Tmp, 0))
			buffer.writeu32(Y, 4, buffer.readu32(Tmp, 4))
			buffer.writeu32(Y, 8, buffer.readu32(Tmp, 8))
			buffer.writeu32(Y, 12, buffer.readu32(Tmp, 12))
		end

		if XPos < XLen then
			local Last = XLen - XPos
			buffer.writeu32(Tmp, 0, 0)
			buffer.writeu32(Tmp, 4, 0)
			buffer.writeu32(Tmp, 8, 0)
			buffer.writeu32(Tmp, 12, 0)
			buffer.copy(Tmp, 0, X, XPos, Last)

			buffer.writeu32(Y, 0, bit32.bxor(buffer.readu32(Y, 0), buffer.readu32(Tmp, 0)))
			buffer.writeu32(Y, 4, bit32.bxor(buffer.readu32(Y, 4), buffer.readu32(Tmp, 4)))
			buffer.writeu32(Y, 8, bit32.bxor(buffer.readu32(Y, 8), buffer.readu32(Tmp, 8)))
			buffer.writeu32(Y, 12, bit32.bxor(buffer.readu32(Y, 12), buffer.readu32(Tmp, 12)))

			GfMult(Y, Tables, Tmp)

			buffer.writeu32(Y, 0, buffer.readu32(Tmp, 0))
			buffer.writeu32(Y, 4, buffer.readu32(Tmp, 4))
			buffer.writeu32(Y, 8, buffer.readu32(Tmp, 8))
			buffer.writeu32(Y, 12, buffer.readu32(Tmp, 12))
		end
	end

	local function Gctr(RoundKeys: buffer, KeyMaterialLength: number, ICB: buffer, X: buffer, XLen: number, Y: buffer)
		if XLen == 0 then
			return
		end

		local N = math.floor(XLen / 16)
		local CB = buffer.create(16)
		local Tmp = buffer.create(16)
		local XPos = 0
		local YPos = 0

		buffer.writeu32(CB, 0, buffer.readu32(ICB, 0))
		buffer.writeu32(CB, 4, buffer.readu32(ICB, 4))
		buffer.writeu32(CB, 8, buffer.readu32(ICB, 8))
		buffer.writeu32(CB, 12, buffer.readu32(ICB, 12))

		local Encrypt = EncryptBlock

		for I = 0, N - 1 do
			Encrypt(RoundKeys, KeyMaterialLength, CB, 0, Tmp, 0)

			buffer.writeu32(Y, YPos + 0, bit32.bxor(buffer.readu32(X, XPos + 0), buffer.readu32(Tmp, 0)))
			buffer.writeu32(Y, YPos + 4, bit32.bxor(buffer.readu32(X, XPos + 4), buffer.readu32(Tmp, 4)))
			buffer.writeu32(Y, YPos + 8, bit32.bxor(buffer.readu32(X, XPos + 8), buffer.readu32(Tmp, 8)))
			buffer.writeu32(Y, YPos + 12, bit32.bxor(buffer.readu32(X, XPos + 12), buffer.readu32(Tmp, 12)))

			XPos += 16
			YPos += 16

			local Val = bit32.byteswap(buffer.readu32(CB, 12))
			Val = (Val + 1) % 0x100000000
			buffer.writeu32(CB, 12, bit32.byteswap(Val))
		end

		local Last = XLen - XPos
		if Last > 0 then
			EncryptBlock(RoundKeys, KeyMaterialLength, CB, 0, Tmp, 0)
			for I = 0, Last - 1 do
				local XByte = buffer.readu8(X, XPos + I)
				local TmpByte = buffer.readu8(Tmp, I)
				buffer.writeu8(Y, YPos + I, bit32.bxor(XByte, TmpByte))
			end
		end
	end

	local function PrepareJ0(H: buffer, IV: buffer, IVLen: number, J0: buffer): buffer
		local Tables = BuildShoupTables(H)

		if IVLen == 12 then
			buffer.writeu32(J0, 0, buffer.readu32(IV, 0))
			buffer.writeu32(J0, 4, buffer.readu32(IV, 4))
			buffer.writeu32(J0, 8, buffer.readu32(IV, 8))
			buffer.writeu32(J0, 12, 0x01000000)
		else
			buffer.writeu32(J0, 0, 0)
			buffer.writeu32(J0, 4, 0)
			buffer.writeu32(J0, 8, 0)
			buffer.writeu32(J0, 12, 0)

			Ghash(Tables, IV, IVLen, J0)

			local LenBuf = buffer.create(16)
			local IVLenBits = IVLen * 8

			buffer.writeu32(LenBuf, 0, 0)
			buffer.writeu32(LenBuf, 4, 0)
			buffer.writeu32(LenBuf, 8, 0)
			buffer.writeu32(LenBuf, 12, bit32.byteswap(IVLenBits))

			Ghash(Tables, LenBuf, 16, J0)
		end

		return Tables
	end

	local function GcmGctr(
		RoundKeys: buffer,
		KeyMaterialLength: number,
		J0: buffer,
		Input: buffer,
		Len: number,
		Output: buffer
	)
		if Len == 0 then
			return
		end

		local J0Inc = buffer.create(16)

		buffer.writeu32(J0Inc, 0, buffer.readu32(J0, 0))
		buffer.writeu32(J0Inc, 4, buffer.readu32(J0, 4))
		buffer.writeu32(J0Inc, 8, buffer.readu32(J0, 8))
		buffer.writeu32(J0Inc, 12, buffer.readu32(J0, 12))

		local Val = bit32.byteswap(buffer.readu32(J0Inc, 12))
		Val = (Val + 1) % 0x100000000
		buffer.writeu32(J0Inc, 12, bit32.byteswap(Val))

		Gctr(RoundKeys, KeyMaterialLength, J0Inc, Input, Len, Output)
	end

	local function GcmHash(Tables: buffer, AAD: buffer, AADLen: number, Crypt: buffer, CryptLen: number, S: buffer)
		local Tmp = buffer.create(16)
		local GfMult = GfMult

		buffer.writeu32(S, 0, 0)
		buffer.writeu32(S, 4, 0)
		buffer.writeu32(S, 8, 0)
		buffer.writeu32(S, 12, 0)

		local M = math.floor(AADLen / 16)
		local XPos = 0

		for _ = 1, M do
			buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(AAD, XPos)))
			buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(AAD, XPos + 4)))
			buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(AAD, XPos + 8)))
			buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(AAD, XPos + 12)))
			XPos += 16

			GfMult(S, Tables, Tmp)

			buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
			buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
			buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
			buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
		end

		if XPos < AADLen then
			local Last = AADLen - XPos
			buffer.writeu32(Tmp, 0, 0)
			buffer.writeu32(Tmp, 4, 0)
			buffer.writeu32(Tmp, 8, 0)
			buffer.writeu32(Tmp, 12, 0)
			buffer.copy(Tmp, 0, AAD, XPos, Last)

			buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(Tmp, 0)))
			buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(Tmp, 4)))
			buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(Tmp, 8)))
			buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(Tmp, 12)))

			GfMult(S, Tables, Tmp)

			buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
			buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
			buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
			buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
		end

		M = math.floor(CryptLen / 16)
		XPos = 0

		for _ = 1, M do
			buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(Crypt, XPos)))
			buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(Crypt, XPos + 4)))
			buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(Crypt, XPos + 8)))
			buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(Crypt, XPos + 12)))
			XPos += 16

			GfMult(S, Tables, Tmp)

			buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
			buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
			buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
			buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
		end

		if XPos < CryptLen then
			local Last = CryptLen - XPos
			buffer.writeu32(Tmp, 0, 0)
			buffer.writeu32(Tmp, 4, 0)
			buffer.writeu32(Tmp, 8, 0)
			buffer.writeu32(Tmp, 12, 0)
			buffer.copy(Tmp, 0, Crypt, XPos, Last)

			buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(Tmp, 0)))
			buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(Tmp, 4)))
			buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(Tmp, 8)))
			buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(Tmp, 12)))

			GfMult(S, Tables, Tmp)

			buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
			buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
			buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
			buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
		end

		local AADLenBits = AADLen * 8
		local CryptLenBits = CryptLen * 8

		buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), bit32.byteswap(AADLenBits)))
		buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), bit32.byteswap(CryptLenBits)))

		GfMult(S, Tables, Tmp)

		buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
		buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
		buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
		buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
	end

	function AES.Encrypt(Plaintext: buffer, Key: buffer, IV: buffer, AAD: buffer?): (buffer, buffer)
		if not Key or typeof(Key) ~= "buffer" then
			error("Key must be a buffer", 2)
		end

		if not IV or typeof(IV) ~= "buffer" then
			error("IV must be a buffer", 2)
		end

		if not Plaintext or typeof(Plaintext) ~= "buffer" then
			error("Plaintext must be a buffer", 2)
		end

		local KeyLength = buffer.len(Key)

		if KeyLength ~= 16 and KeyLength ~= 24 and KeyLength ~= 32 then
			error("Key must be 16, 24, or 32 bytes", 2)
		end

		local KeyConfig = KEY_CONFIGS[KeyLength]
		local RoundKeys = ExpandKeySchedule(Key, KeyLength, buffer.create(KeyConfig.ExpandedLength))
		local KeyMaterialLength = KeyConfig.MaterialLength

		local IVLen = buffer.len(IV)
		local AADLen = buffer.len(AAD or buffer.create(0))
		local PlainLen = buffer.len(Plaintext)
		local AuthData = AAD or buffer.create(0)

		local OutputBuffer = buffer.create(PlainLen)
		local OutputTag = buffer.create(16)

		local H = buffer.create(16)
		local J0 = buffer.create(16)
		local S = buffer.create(16)

		EncryptBlock(RoundKeys, KeyMaterialLength, H, 0, H, 0)
		local Tables = PrepareJ0(H, IV, IVLen, J0)
		GcmGctr(RoundKeys, KeyMaterialLength, J0, Plaintext, PlainLen, OutputBuffer)
		GcmHash(Tables, AuthData, AADLen, OutputBuffer, PlainLen, S)
		Gctr(RoundKeys, KeyMaterialLength, J0, S, 16, OutputTag)

		return OutputBuffer, OutputTag
	end

	function AES.Decrypt(Ciphertext: buffer, Key: buffer, IV: buffer, Tag: buffer, AAD: buffer?): (boolean, buffer?)
		if not Key or typeof(Key) ~= "buffer" then
			error("Key must be a buffer", 2)
		end

		if not IV or typeof(IV) ~= "buffer" then
			error("IV must be a buffer", 2)
		end

		if not Ciphertext or typeof(Ciphertext) ~= "buffer" then
			error("Ciphertext must be a buffer", 2)
		end

		if not Tag or typeof(Tag) ~= "buffer" then
			error("Tag must be a buffer", 2)
		end

		local KeyLength = buffer.len(Key)
		if KeyLength ~= 16 and KeyLength ~= 24 and KeyLength ~= 32 then
			error("Key must be 16, 24, or 32 bytes", 2)
		end

		local KeyConfig = KEY_CONFIGS[KeyLength]
		local RoundKeys = ExpandKeySchedule(Key, KeyLength, buffer.create(KeyConfig.ExpandedLength))
		local KeyMaterialLength = KeyConfig.MaterialLength

		local IVLen = buffer.len(IV)
		local AADLen = buffer.len(AAD or buffer.create(0))
		local CryptLen = buffer.len(Ciphertext)
		local AuthData = AAD or buffer.create(0)

		local OutputBuffer = buffer.create(CryptLen)

		local H = buffer.create(16)
		local J0 = buffer.create(16)
		local S = buffer.create(16)
		local ComputedTag = buffer.create(16)

		EncryptBlock(RoundKeys, KeyMaterialLength, H, 0, H, 0)
		local Tables = PrepareJ0(H, IV, IVLen, J0)
		GcmGctr(RoundKeys, KeyMaterialLength, J0, Ciphertext, CryptLen, OutputBuffer)
		GcmHash(Tables, AuthData, AADLen, Ciphertext, CryptLen, S)
		Gctr(RoundKeys, KeyMaterialLength, J0, S, 16, ComputedTag)

		if not ConstantTimeCompare(Tag, ComputedTag) then
			return false, nil
		end

		return true, OutputBuffer
	end

	Encryption.AES = AES
end

local Cryptography: typeCryptography = {
	Encryption = Encryption,
	Funcs = Funcs,
	Utils = Utils,
}

return table.freeze(Cryptography)