# AES-GCM for Roblox Executor

## Overview

<p>
This is a simplified AES-GCM implementation designed specifically for
Roblox executors and Lune environments.\
This pertains to the AES functionality of <a href="https://github.com/daily3014/rbx-cryptography" >rbx-cryptography</a>, but trimmed down to only include the necessary parts
required for AES usage in scripts.

Do not expect a full cryptography suite.\
This module focuses on practicality, portability, and ease of
integration in executor-based environments.
</p>

------------------------------------------------------------------------

## Why This Module?

This project extracts only the essential components and packages them
into a single, lightweight module that can be easily used in:

-   Roblox (executors environment)
-   Lune environment

------------------------------------------------------------------------

## Installation

### Lune Environment

``` lua
local Cryptography = require("./module")
```

### Roblox Executor Environment

``` lua
local Cryptography = loadstring(game:HttpGet("YOUR_MODULE_LINK"))()
```

------------------------------------------------------------------------

## Module Access

``` lua
local AES = Cryptography.Encryption.AES
local CSPRNG = Cryptography.Utils.CSPRNG
local Conversions = Cryptography.Utils.Conversions
```

------------------------------------------------------------------------

## API Documentation

### AES (GCM)

Provides authenticated encryption and decryption using AES-GCM.

#### Encrypt

``` lua
AES.Encrypt(Plaintext: buffer, Key: buffer, IV: buffer, AAD: buffer?) -> (buffer, buffer)
```

**Parameters:** - Plaintext (buffer): Data to encrypt - Key (buffer):
AES key (16, 24, or 32 bytes) - IV (buffer): Initialization Vector
(recommended: 12 bytes) - AAD (buffer, optional): Additional
Authenticated Data

**Returns:** - Ciphertext (buffer) - Authentication Tag (buffer)

------------------------------------------------------------------------

#### Decrypt

``` lua
AES.Decrypt(Ciphertext: buffer, Key: buffer, IV: buffer, Tag: buffer, AAD: buffer?) -> (boolean, buffer?)
```

**Returns:** - Success (boolean): Indicates if authentication passed -
Decrypted (buffer?): Decrypted data (only if successful)

------------------------------------------------------------------------

### Conversions

Utility functions for buffer and hexadecimal conversions.

``` lua
Conversions.ToHex(Buffer: buffer) -> string
Conversions.FromHex(Hex: string | buffer) -> buffer
```

------------------------------------------------------------------------

### CSPRNG (Cryptographically Secure Random)

Secure random generation utilities.

``` lua
CSPRNG.Random() -> number
CSPRNG.RandomInt(Min: number, Max: number?) -> number
CSPRNG.RandomNumber(Min: number, Max: number?) -> number
CSPRNG.RandomBytes(Count: number) -> buffer
CSPRNG.RandomString(Length: number, AsBuffer: boolean?) -> string | buffer
CSPRNG.RandomHex(Length: number) -> string
CSPRNG.Ed25519ClampedBytes(Input: buffer) -> buffer
CSPRNG.Ed25519Random() -> buffer
```

------------------------------------------------------------------------

## Full Usage Example

``` lua
--local Cryptography = require("./module") -- (for lune environment)
local Cryptography = loadstring(game:HttpGet("https://github.com"))() -- (for roblox executor environment)

local AES = Cryptography.Encryption.AES
local CSPRNG = Cryptography.Utils.CSPRNG
local Conversions = Cryptography.Utils.Conversions

local Key = CSPRNG.RandomBytes(32) -- 16, 24, or 32 bytes
local IV = CSPRNG.RandomBytes(12) -- required value (recommended for GCM)

local Message = "This is a secret message"
local Plaintext = buffer.fromstring(Message)

-- Optional Additional Authenticated Data (AAD)
local AAD = buffer.fromstring("user:john,timestamp:456745683")

local Encrypted, Tag = AES.Encrypt(Plaintext, Key, IV, AAD)
local Success, Decrypted = AES.Decrypt(Encrypted, Key, IV, Tag, AAD)

if Success then
    print("Show key:", Key) -- type: buffer
    print("Show Encrypted:", Encrypted) -- type: buffer
    print("Show Tag:", Tag) -- type: buffer

    print("Show Key in hex:", Conversions.ToHex(Key)) -- type: string (hex)
    print("Show Encrypted in hex:", Conversions.ToHex(Encrypted)) -- type: string (hex)
    print("Show Tag in hex:", Conversions.ToHex(Tag)) -- type: string (hex)

    print("Show Decrypted:", Decrypted) -- type: buffer
    print("Show Decrypted in string:", buffer.tostring(Decrypted)) -- type: string
end
```

------------------------------------------------------------------------

## Notes

-   Always use a unique IV for each encryption.
-   Never reuse the same Key + IV combination.
-   Recommended IV size for AES-GCM is 12 bytes.
-   This module is intended for scripting convenience, not
    enterprise-grade security.