--local Cryptography = require("./module") --(for lune environment)
local Cryptography = loadstring(game:HttpGet("https://github.com"))() -- (for roblox executor environment)

local AES = Cryptography.Encryption.AES
local CSPRNG = Cryptography.Utils.CSPRNG
local Conversions = Cryptography.Utils.Conversions

--[[

    AES:
        {
            Encrypt: (Plaintext: buffer, Key: buffer, IV: buffer, AAD: buffer?) -> (buffer, buffer),
            Decrypt: (Ciphertext: buffer, Key: buffer, IV: buffer, Tag: buffer, AAD: buffer?) -> (boolean, buffer?)
        }

    Conversions:
        {
            ToHex: (Buffer: buffer) -> string,
            FromHex: (Hex: string | buffer) -> buffer
        }

    CSPRNG:
        {
            Random: () -> number,
            RandomInt: (Min: number, Max: number?) -> number,
            RandomNumber: (Min: number, Max: number?) -> number,
            RandomBytes: (Count: number) -> buffer,
            RandomString: (Length: number, AsBuffer: boolean?) -> string | buffer,
            RandomHex: (Length: number) -> string,
            Ed25519ClampedBytes: (Input: buffer) -> buffer,
            Ed25519Random: () -> buffer
        }

]]

local Key = CSPRNG.RandomBytes(32) -- 16, 24, 32 bytes
local IV = CSPRNG.RandomBytes(12) -- required value

local Message = "This is a secret message"
local Plaintext = buffer.fromstring(Message)

local AAD = buffer.fromstring("user:john,timestamp:456745683") -- (optional value)

local Encrypted, Tag = AES.Encrypt(Plaintext, Key, IV, AAD)
local Success, Decrypted = AES.Decrypt(Encrypted, Key, IV, Tag, AAD)

if Success then

    print("Show key:", Key) -- type buffer
    print("Show Encrypted:", Encrypted) -- type buffer
    print("Show Tag:", Tag) -- type buffer
    
    print("Show Key in hex:", Conversions.ToHex(Key)) -- type string hex
    print("Show Encrypted in hex:", Conversions.ToHex(Encrypted)) -- type string hex
    print("Show Tag in hex:", Conversions.ToHex(Tag)) -- type string

    print("Show Decrypted:", Decrypted) -- type buffer
    print("Show Decrypted in string:", buffer.tostring(Decrypted)) -- type string

end