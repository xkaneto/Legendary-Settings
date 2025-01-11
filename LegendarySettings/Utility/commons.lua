local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
    return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
    local DIP = 1;
    local repeatNext;
    ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
        if (Byte(byte, 2) == 81) then
            repeatNext = StrToNumber(Sub(byte, 1, 1));
            return "";
        else
            local a = Char(StrToNumber(byte, 16));
            if repeatNext then
                local b = Rep(a, repeatNext);
                repeatNext = nil;
                return b;
            else
                return a;
            end
        end
    end);
    local function gBit(Bit, Start, End)
        if End then
            local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
            return Res - (Res % 1);
        else
            local Plc = 2 ^ (Start - 1);
            return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
        end
    end
    local function gBits8()
        local a = Byte(ByteString, DIP, DIP);
        DIP = DIP + 1;
        return a;
    end
    local function gBits16()
        local a, b = Byte(ByteString, DIP, DIP + 2);
        DIP = DIP + 2;
        return (b * 256) + a;
    end
    local function gBits32()
        local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
        DIP = DIP + 4;
        return (d * 16777216) + (c * 65536) + (b * 256) + a;
    end
    local function gFloat()
        local Left = gBits32();
        local Right = gBits32();
        local IsNormal = 1;
        local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
        local Exponent = gBit(Right, 21, 31);
        local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
        if (Exponent == 0) then
            if (Mantissa == 0) then
                return Sign * 0;
            else
                Exponent = 1;
                IsNormal = 0;
            end
        elseif (Exponent == 2047) then
            return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
        end
        return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
    end
    local function gString(Len)
        local Str;
        if not Len then
            Len = gBits32();
            if (Len == 0) then
                return "";
            end
        end
        Str = Sub(ByteString, DIP, (DIP + Len) - 1);
        DIP = DIP + Len;
        local FStr = {};
        for Idx = 1, #Str do
            FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
        end
        return Concat(FStr);
    end
    local gInt = gBits32;
    local function _R(...)
        return {...}, Select("#", ...);
    end
    local function Deserialize()
        local Instrs = {};
        local Functions = {};
        local Lines = {};
        local Chunk = {Instrs, Functions, nil, Lines};
        local ConstCount = gBits32();
        local Consts = {};
        for Idx = 1, ConstCount do
            local Type = gBits8();
            local Cons;
            if (Type == 1) then
                Cons = gBits8() ~= 0;
            elseif (Type == 2) then
                Cons = gFloat();
            elseif (Type == 3) then
                Cons = gString();
            end
            Consts[Idx] = Cons;
        end
        Chunk[3] = gBits8();
        for Idx = 1, gBits32() do
            local Descriptor = gBits8();
            if (gBit(Descriptor, 1, 1) == 0) then
                local Type = gBit(Descriptor, 2, 3);
                local Mask = gBit(Descriptor, 4, 6);
                local Inst = {gBits16(), gBits16(), nil, nil};
                if (Type == 0) then
                    Inst[3] = gBits16();
                    Inst[4] = gBits16();
                elseif (Type == 1) then
                    Inst[3] = gBits32();
                elseif (Type == 2) then
                    Inst[3] = gBits32() - (2 ^ 16);
                elseif (Type == 3) then
                    Inst[3] = gBits32() - (2 ^ 16);
                    Inst[4] = gBits16();
                end
                if (gBit(Mask, 1, 1) == 1) then
                    Inst[2] = Consts[Inst[2]];
                end
                if (gBit(Mask, 2, 2) == 1) then
                    Inst[3] = Consts[Inst[3]];
                end
                if (gBit(Mask, 3, 3) == 1) then
                    Inst[4] = Consts[Inst[4]];
                end
                Instrs[Idx] = Inst;
            end
        end
        for Idx = 1, gBits32() do
            Functions[Idx - 1] = Deserialize();
        end
        return Chunk;
    end
    local function Wrap(Chunk, Upvalues, Env)
        local Instr = Chunk[1];
        local Proto = Chunk[2];
        local Params = Chunk[3];
        return function(...)
            local Instr = Instr;
            local Proto = Proto;
            local Params = Params;
            local _R = _R;
            local VIP = 1;
            local Top = -1;
            local Vararg = {};
            local Args = {...};
            local PCount = Select("#", ...) - 1;
            local Lupvals = {};
            local Stk = {};
            for Idx = 0, PCount do
                if (Idx >= Params) then
                    Vararg[Idx - Params] = Args[Idx + 1];
                else
                    Stk[Idx] = Args[Idx + 1];
                end
            end
            local Varargsz = (PCount - Params) + 1;
            local Inst;
            local Enum;
            while true do
                Inst = Instr[VIP];
                Enum = Inst[1];
                if (Enum <= 99) then
                    if (Enum <= 49) then
                        if (Enum <= 24) then
                            if (Enum <= 11) then
                                if (Enum <= 5) then
                                    if (Enum <= 2) then
                                        if (Enum <= 0) then
                                            local A;
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Upvalues[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                        elseif (Enum > 1) then
                                            local A;
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Stk[A + 1]);
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if (Stk[Inst[2]] ~= Inst[4]) then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        else
                                            Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                        end
                                    elseif (Enum <= 3) then
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                    elseif (Enum == 4) then
                                        local Results;
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                        Edx = 0;
                                        for Idx = A, Inst[4] do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        do
                                            return Stk[Inst[2]];
                                        end
                                    end
                                elseif (Enum <= 8) then
                                    if (Enum <= 6) then
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Stk[A + 1]);
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] <= Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    elseif (Enum > 7) then
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if not Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        Stk[Inst[2]] = Env[Inst[3]];
                                    end
                                elseif (Enum <= 9) then
                                    local A;
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                elseif (Enum == 10) then
                                    local B;
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Stk[A + 1]));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    B = Stk[Inst[4]];
                                    if B then
                                        VIP = VIP + 1;
                                    else
                                        Stk[Inst[2]] = B;
                                        VIP = Inst[3];
                                    end
                                else
                                    local A = Inst[2];
                                    Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                end
                            elseif (Enum <= 17) then
                                if (Enum <= 14) then
                                    if (Enum <= 12) then
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                    elseif (Enum == 13) then
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Stk[A + 1]);
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] <= Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A]();
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        VIP = Inst[3];
                                    end
                                elseif (Enum <= 15) then
                                    local B;
                                    local A;
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    B = Stk[Inst[3]];
                                    Stk[A + 1] = B;
                                    Stk[A] = B[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    B = Stk[Inst[3]];
                                    Stk[A + 1] = B;
                                    Stk[A] = B[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    B = Stk[Inst[3]];
                                    Stk[A + 1] = B;
                                    Stk[A] = B[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = #Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Inst[2] < Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 16) then
                                    local Edx;
                                    local Results;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Stk[A + 1])};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    Stk[Inst[2]] = {};
                                end
                            elseif (Enum <= 20) then
                                if (Enum <= 18) then
                                    local B = Inst[3];
                                    local K = Stk[B];
                                    for Idx = B + 1, Inst[4] do
                                        K = K .. Stk[Idx];
                                    end
                                    Stk[Inst[2]] = K;
                                elseif (Enum > 19) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                end
                            elseif (Enum <= 22) then
                                if (Enum == 21) then
                                    for Idx = Inst[2], Inst[3] do
                                        Stk[Idx] = nil;
                                    end
                                elseif (Stk[Inst[2]] < Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 23) then
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                            end
                        elseif (Enum <= 36) then
                            if (Enum <= 30) then
                                if (Enum <= 27) then
                                    if (Enum <= 25) then
                                        local A = Inst[2];
                                        Stk[A](Stk[A + 1]);
                                    elseif (Enum > 26) then
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                    else
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum <= 28) then
                                    local A = Inst[2];
                                    local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    local Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                elseif (Enum == 29) then
                                    local Results;
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 33) then
                                if (Enum <= 31) then
                                    local B;
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Stk[A + 1]));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    B = Stk[Inst[4]];
                                    if B then
                                        VIP = VIP + 1;
                                    else
                                        Stk[Inst[2]] = B;
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 32) then
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum <= 34) then
                                local A = Inst[2];
                                local Cls = {};
                                for Idx = 1, #Lupvals do
                                    local List = Lupvals[Idx];
                                    for Idz = 0, #List do
                                        local Upv = List[Idz];
                                        local NStk = Upv[1];
                                        local DIP = Upv[2];
                                        if ((NStk == Stk) and (DIP >= A)) then
                                            Cls[DIP] = NStk[DIP];
                                            Upv[1] = Cls;
                                        end
                                    end
                                end
                            elseif (Enum > 35) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                do
                                    return Unpack(Stk, A, A + Inst[3]);
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                do
                                    return;
                                end
                            end
                        elseif (Enum <= 42) then
                            if (Enum <= 39) then
                                if (Enum <= 37) then
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum == 38) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    do
                                        return Stk[Inst[2]];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    do
                                        return;
                                    end
                                else
                                    local A = Inst[2];
                                    local Results = {Stk[A](Stk[A + 1])};
                                    local Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                end
                            elseif (Enum <= 40) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 41) then
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local B;
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            end
                        elseif (Enum <= 45) then
                            if (Enum <= 43) then
                                Stk[Inst[2]] = Inst[3] ~= 0;
                                VIP = VIP + 1;
                            elseif (Enum > 44) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            else
                                local A = Inst[2];
                                local B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                            end
                        elseif (Enum <= 47) then
                            if (Enum == 46) then
                                if (Stk[Inst[2]] <= Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum == 48) then
                            local A;
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                        else
                            local A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        end
                    elseif (Enum <= 74) then
                        if (Enum <= 61) then
                            if (Enum <= 55) then
                                if (Enum <= 52) then
                                    if (Enum <= 50) then
                                        Stk[Inst[2]] = #Stk[Inst[3]];
                                    elseif (Enum > 51) then
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    else
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        VIP = Inst[3];
                                    end
                                elseif (Enum <= 53) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum == 54) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 58) then
                                if (Enum <= 56) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum == 57) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 59) then
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum > 60) then
                                local B;
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Stk[A + 1]);
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] <= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 67) then
                            if (Enum <= 64) then
                                if (Enum <= 62) then
                                    local A = Inst[2];
                                    local Step = Stk[A + 2];
                                    local Index = Stk[A] + Step;
                                    Stk[A] = Index;
                                    if (Step > 0) then
                                        if (Index <= Stk[A + 1]) then
                                            VIP = Inst[3];
                                            Stk[A + 3] = Index;
                                        end
                                    elseif (Index >= Stk[A + 1]) then
                                        VIP = Inst[3];
                                        Stk[A + 3] = Index;
                                    end
                                elseif (Enum == 63) then
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 65) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 66) then
                                local Edx;
                                local Results, Limit;
                                local B;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            else
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 70) then
                            if (Enum <= 68) then
                                local A;
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum > 69) then
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 72) then
                            if (Enum == 71) then
                                if (Inst[2] < Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum == 73) then
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        end
                    elseif (Enum <= 86) then
                        if (Enum <= 80) then
                            if (Enum <= 77) then
                                if (Enum <= 75) then
                                    Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
                                elseif (Enum > 76) then
                                    local A = Inst[2];
                                    local T = Stk[A];
                                    for Idx = A + 1, Inst[3] do
                                        Insert(T, Stk[Idx]);
                                    end
                                else
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                end
                            elseif (Enum <= 78) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            elseif (Enum == 79) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A = Inst[2];
                                do
                                    return Unpack(Stk, A, A + Inst[3]);
                                end
                            end
                        elseif (Enum <= 83) then
                            if (Enum <= 81) then
                                if (Inst[2] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 82) then
                                if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            end
                        elseif (Enum <= 84) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 85) then
                            Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
                        else
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 92) then
                        if (Enum <= 89) then
                            if (Enum <= 87) then
                                if (Stk[Inst[2]] ~= Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum > 88) then
                                local Edx;
                                local Results;
                                local B;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results = {Stk[A](Stk[A + 1])};
                                Edx = 0;
                                for Idx = A, Inst[4] do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] < Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            end
                        elseif (Enum <= 90) then
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 91) then
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = #Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                        end
                    elseif (Enum <= 95) then
                        if (Enum <= 93) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum == 94) then
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 97) then
                        if (Enum == 96) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum > 98) then
                        Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
                    else
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum <= 149) then
                    if (Enum <= 124) then
                        if (Enum <= 111) then
                            if (Enum <= 105) then
                                if (Enum <= 102) then
                                    if (Enum <= 100) then
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if not Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    elseif (Enum > 101) then
                                        local Edx;
                                        local Results, Limit;
                                        local B;
                                        local A;
                                        A = Inst[2];
                                        B = Inst[3];
                                        for Idx = A, B do
                                            Stk[Idx] = Vararg[Idx - A];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        B = Stk[Inst[3]];
                                        Stk[A + 1] = B;
                                        Stk[A] = B[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        B = Stk[Inst[3]];
                                        Stk[A + 1] = B;
                                        Stk[A] = B[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                    else
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if not Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum <= 103) then
                                    local Limit;
                                    local Results;
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A]()};
                                    Limit = Inst[4];
                                    Edx = 0;
                                    for Idx = A, Limit do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                elseif (Enum == 104) then
                                    local A = Inst[2];
                                    local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
                                    Top = (Limit + A) - 1;
                                    local Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                else
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                end
                            elseif (Enum <= 108) then
                                if (Enum <= 106) then
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 107) then
                                    local A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 109) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            elseif (Enum > 110) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A = Inst[2];
                                Stk[A] = Stk[A]();
                            end
                        elseif (Enum <= 117) then
                            if (Enum <= 114) then
                                if (Enum <= 112) then
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum == 113) then
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = {};
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                end
                            elseif (Enum <= 115) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum > 116) then
                                local A = Inst[2];
                                local Results, Limit = _R(Stk[A](Stk[A + 1]));
                                Top = (Limit + A) - 1;
                                local Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 120) then
                            if (Enum <= 118) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 119) then
                                if (Stk[Inst[2]] <= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                            end
                        elseif (Enum <= 122) then
                            if (Enum > 121) then
                                Stk[Inst[2]] = Inst[3];
                            else
                                local B;
                                local A;
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            end
                        elseif (Enum > 123) then
                            do
                                return;
                            end
                        else
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 136) then
                        if (Enum <= 130) then
                            if (Enum <= 127) then
                                if (Enum <= 125) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum == 126) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Inst[2] < Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A = Inst[2];
                                    do
                                        return Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    end
                                end
                            elseif (Enum <= 128) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Stk[A + 1]);
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            elseif (Enum > 129) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 133) then
                            if (Enum <= 131) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            elseif (Enum == 132) then
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            else
                                local A;
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            end
                        elseif (Enum <= 134) then
                            local Results;
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 135) then
                            local A = Inst[2];
                            local T = Stk[A];
                            local B = Inst[3];
                            for Idx = 1, B do
                                T[Idx] = Stk[A + Idx];
                            end
                        else
                            local Results;
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]]();
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]]();
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]]();
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 142) then
                        if (Enum <= 139) then
                            if (Enum <= 137) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Stk[A + 1]);
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            elseif (Enum > 138) then
                                local A = Inst[2];
                                local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                local Edx = 0;
                                for Idx = A, Inst[4] do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 140) then
                            local A = Inst[2];
                            local Results = {Stk[A]()};
                            local Limit = Inst[4];
                            local Edx = 0;
                            for Idx = A, Limit do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                        elseif (Enum > 141) then
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        else
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 145) then
                        if (Enum <= 143) then
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 144) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local A;
                            A = Inst[2];
                            Stk[A] = Stk[A]();
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 147) then
                        if (Enum == 146) then
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local Limit;
                            local Results;
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Stk[A + 1]);
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A]()};
                            Limit = Inst[4];
                            Edx = 0;
                            for Idx = A, Limit do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                        end
                    elseif (Enum == 148) then
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Stk[A + 1]);
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                    else
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum <= 174) then
                    if (Enum <= 161) then
                        if (Enum <= 155) then
                            if (Enum <= 152) then
                                if (Enum <= 150) then
                                    local A;
                                    A = Inst[2];
                                    Stk[A] = Stk[A]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 151) then
                                    local B;
                                    local T;
                                    local A;
                                    A = Inst[2];
                                    Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    for Idx = Inst[2], Inst[3] do
                                        Stk[Idx] = nil;
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = {};
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    T = Stk[A];
                                    B = Inst[3];
                                    for Idx = 1, B do
                                        T[Idx] = Stk[A + Idx];
                                    end
                                else
                                    local A = Inst[2];
                                    local B = Inst[3];
                                    for Idx = A, B do
                                        Stk[Idx] = Vararg[Idx - A];
                                    end
                                end
                            elseif (Enum <= 153) then
                                local Results;
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                Edx = 0;
                                for Idx = A, Inst[4] do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            elseif (Enum == 154) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            else
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 158) then
                            if (Enum <= 156) then
                                local A = Inst[2];
                                do
                                    return Unpack(Stk, A, Top);
                                end
                            elseif (Enum > 157) then
                                local Step;
                                local Index;
                                local A;
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Index = Stk[A];
                                Step = Stk[A + 2];
                                if (Step > 0) then
                                    if (Index > Stk[A + 1]) then
                                        VIP = Inst[3];
                                    else
                                        Stk[A + 3] = Index;
                                    end
                                elseif (Index < Stk[A + 1]) then
                                    VIP = Inst[3];
                                else
                                    Stk[A + 3] = Index;
                                end
                            else
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 159) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        elseif (Enum > 160) then
                            local A = Inst[2];
                            local Index = Stk[A];
                            local Step = Stk[A + 2];
                            if (Step > 0) then
                                if (Index > Stk[A + 1]) then
                                    VIP = Inst[3];
                                else
                                    Stk[A + 3] = Index;
                                end
                            elseif (Index < Stk[A + 1]) then
                                VIP = Inst[3];
                            else
                                Stk[A + 3] = Index;
                            end
                        else
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 167) then
                        if (Enum <= 164) then
                            if (Enum <= 162) then
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Stk[A + 1]));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                            elseif (Enum == 163) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Stk[A + 1]);
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 165) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Stk[A + 1]);
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 166) then
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 170) then
                        if (Enum <= 168) then
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 169) then
                            local Results;
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local A = Inst[2];
                            local C = Inst[4];
                            local CB = A + 2;
                            local Result = {Stk[A](Stk[A + 1], Stk[CB])};
                            for Idx = 1, C do
                                Stk[CB + Idx] = Result[Idx];
                            end
                            local R = Result[1];
                            if R then
                                Stk[CB] = R;
                                VIP = Inst[3];
                            else
                                VIP = VIP + 1;
                            end
                        end
                    elseif (Enum <= 172) then
                        if (Enum > 171) then
                            local B = Stk[Inst[4]];
                            if B then
                                VIP = VIP + 1;
                            else
                                Stk[Inst[2]] = B;
                                VIP = Inst[3];
                            end
                        else
                            local K;
                            local B;
                            local A;
                            A = Inst[2];
                            B = Stk[Inst[3]];
                            Stk[A + 1] = B;
                            Stk[A] = B[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Stk[A + 1]);
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            B = Inst[3];
                            K = Stk[B];
                            for Idx = B + 1, Inst[4] do
                                K = K .. Stk[Idx];
                            end
                            Stk[Inst[2]] = K;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum > 173) then
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    else
                        local NewProto = Proto[Inst[3]];
                        local NewUvals;
                        local Indexes = {};
                        NewUvals = Setmetatable({}, {
                            __index = function(_, Key)
                                local Val = Indexes[Key];
                                return Val[1][Val[2]];
                            end,
                            __newindex = function(_, Key, Value)
                                local Val = Indexes[Key];
                                Val[1][Val[2]] = Value;
                            end
                        });
                        for Idx = 1, Inst[4] do
                            VIP = VIP + 1;
                            local Mvm = Instr[VIP];
                            if (Mvm[1] == 76) then
                                Indexes[Idx - 1] = {Stk, Mvm[3]};
                            else
                                Indexes[Idx - 1] = {Upvalues, Mvm[3]};
                            end
                            Lupvals[#Lupvals + 1] = Indexes;
                        end
                        Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
                    end
                elseif (Enum <= 186) then
                    if (Enum <= 180) then
                        if (Enum <= 177) then
                            if (Enum <= 175) then
                                Stk[Inst[2]]();
                            elseif (Enum == 176) then
                                local B;
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                B = Stk[Inst[4]];
                                if B then
                                    VIP = VIP + 1;
                                else
                                    Stk[Inst[2]] = B;
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 178) then
                            local A;
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 179) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            Stk[Inst[2]] = {};
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 183) then
                        if (Enum <= 181) then
                            local Edx;
                            local Results;
                            local K;
                            local B;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            B = Inst[3];
                            K = Stk[B];
                            for Idx = B + 1, Inst[4] do
                                K = K .. Stk[Idx];
                            end
                            Stk[Inst[2]] = K;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                        elseif (Enum == 182) then
                            if (Stk[Inst[2]] == Inst[4]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 184) then
                        Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
                    elseif (Enum == 185) then
                        local Step;
                        local Index;
                        local B;
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        for Idx = Inst[2], Inst[3] do
                            Stk[Idx] = nil;
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        B = Stk[Inst[3]];
                        Stk[A + 1] = B;
                        Stk[A] = B[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        B = Stk[Inst[3]];
                        Stk[A + 1] = B;
                        Stk[A] = B[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3] ~= 0;
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3] ~= 0;
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3] ~= 0;
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3] ~= 0;
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3] ~= 0;
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        B = Stk[Inst[3]];
                        Stk[A + 1] = B;
                        Stk[A] = B[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Stk[A + 1]);
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Index = Stk[A];
                        Step = Stk[A + 2];
                        if (Step > 0) then
                            if (Index > Stk[A + 1]) then
                                VIP = Inst[3];
                            else
                                Stk[A + 3] = Index;
                            end
                        elseif (Index < Stk[A + 1]) then
                            VIP = Inst[3];
                        else
                            Stk[A + 3] = Index;
                        end
                    else
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum <= 192) then
                    if (Enum <= 189) then
                        if (Enum <= 187) then
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum == 188) then
                            local Results;
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local Edx;
                            local Results;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Stk[A + 1])};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if (Stk[Inst[2]] ~= Inst[4]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 190) then
                        local A;
                        Stk[Inst[2]] = {};
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    elseif (Enum == 191) then
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    else
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if (Stk[Inst[2]] ~= Inst[4]) then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum <= 195) then
                    if (Enum <= 193) then
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    elseif (Enum == 194) then
                        local A;
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        VIP = Inst[3];
                    else
                        local A = Inst[2];
                        local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
                        local Edx = 0;
                        for Idx = A, Inst[4] do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                    end
                elseif (Enum <= 197) then
                    if (Enum > 196) then
                        local A = Inst[2];
                        Stk[A] = Stk[A](Stk[A + 1]);
                    else
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum > 198) then
                    local A;
                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    Stk[Inst[2]] = Stk[Inst[3]];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    Stk[Inst[2]] = Inst[3];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    A = Inst[2];
                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    if Stk[Inst[2]] then
                        VIP = VIP + 1;
                    else
                        VIP = Inst[3];
                    end
                else
                    local A = Inst[2];
                    Stk[A](Unpack(Stk, A + 1, Top));
                end
                VIP = VIP + 1;
            end
        end;
    end
    return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall(
    "LOL!3B3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403113Q004C6567656E6461727953652Q74696E6773030B3Q00426967576967734461746103083Q00265C4558FC840E4A03063Q00E36B39362B9D028Q0003063Q00B4F5DA8883E903043Q00E6E79AAF03063Q0048724461746103083Q0032F4AAC8FA7D930503073Q00EB7195D9BCAE18034Q00030C3Q00A255E075AAB25CE675A3A86803053Q00CFE12C831903073Q0068CABB401E506403063Q001D2BB3D82C7B010003093Q009EC02340B8EC2E45A903043Q002CDDB94003053Q0035E8435A7D03053Q00136187283F00030A3Q00805327122103AF52343E03063Q0051CE3C535B4F03073Q007DBBD57E23EA6903083Q00C42ECBB0124FA32D030D3Q008C236C1921EFC6B60F7B1221FE03073Q008FD8421E7E449B030D3Q009EC91FCCC0B7FEEF98C903CCC003083Q0081CAA86DABA5C3B7030E3Q00165925DFDB00CF2C6B27D4DF07EE03073Q0086423857B8BE74030B3Q004372656174654672616D6503053Q001A2308B61C03083Q00555C5169DB798B41030D3Q0052656769737465724576656E7403143Q00CD9F717C59EDC281756259F1C2967E645EF3D89703063Q00BF9DD330251C03153Q00EF33D5251FED20C6391DFA31CB3813EC3ED6301FFB03053Q005ABF7F947C03093Q0053657453637269707403073Q0057890B017D893A03043Q007718E74E03053Q00D1E13DDFF203043Q00B297935C03163Q00A1E4603715497488FC5E2B275C7E8DE94914004D778903073Q001AEC9D2C52722C03083Q005549506172656E7403083Q00AABC061B4C4F9D8003073Q00E9E5D2536B282E00943Q0012083Q00013Q00206Q000200122Q000100013Q00202Q00010001000300122Q000200013Q00202Q00020002000400122Q000300053Q00062Q0003000A0001000100048A3Q000A0001001207000300063Q00204A000400030007001207000500083Q00204A000500050009001207000600083Q00204A00060006000A0006AD00073Q000100062Q004C3Q00064Q004C8Q004C3Q00044Q004C3Q00014Q004C3Q00024Q004C3Q00054Q00660008000A3Q00122Q000A000B6Q000B3Q00024Q000C00073Q00122Q000D000D3Q00122Q000E000E6Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00103Q00122Q000E00116Q000C000E000200202Q000B000C000F00102Q000A000C000B4Q000B3Q000A4Q000C00073Q00122Q000D00133Q00122Q000E00146Q000C000E000200202Q000B000C00154Q000C00073Q00122Q000D00163Q00122Q000E00176Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00183Q00122Q000E00196Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D001B3Q00122Q000E001C6Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D001D3Q00122Q000E001E6Q000C000E000200202Q000B000C001F4Q000C00073Q00122Q000D00203Q00122Q000E00216Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D00223Q00122Q000E00236Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00243Q00122Q000E00256Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00263Q00122Q000E00276Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00283Q00122Q000E00296Q000C000E000200202Q000B000C000F00102Q000A0012000B00122Q000B002A6Q000C00073Q00122Q000D002B3Q00122Q000E002C6Q000C000E6Q000B3Q000200202Q000C000B002D4Q000E00073Q00122Q000F002E3Q00122Q0010002F6Q000E00106Q000C3Q000100202Q000C000B002D4Q000E00073Q00122A000F00303Q00122Q001000316Q000E00106Q000C3Q000100202Q000C000B00324Q000E00073Q00122Q000F00333Q00122Q001000346Q000E001000020006AD000F0001000100022Q004C3Q00074Q004C3Q000A4Q000B000C000F00010006AD000C0002000100022Q004C3Q000A4Q004C3Q00073Q001230000D002A6Q000E00073Q00122Q000F00353Q00122Q001000366Q000E001000024Q000F00073Q00122Q001000373Q00122Q001100386Q000F0011000200122Q001000394Q0031000D001000020006AD000E0003000100022Q004C3Q00074Q004C3Q000A3Q0006AD000F0004000100022Q004C3Q00074Q004C3Q000A3Q0020790010000D00324Q001200073Q00122Q0013003A3Q00122Q0014003B6Q0012001400020006AD00130005000100052Q004C3Q000E4Q004C3Q000F4Q004C3Q000C4Q004C3Q00074Q004C3Q000A4Q000B0010001300012Q007C3Q00013Q00063Q00023Q00026Q00F03F026Q00704002264Q009E00025Q00122Q000300016Q00045Q00122Q000500013Q00042Q0003002100012Q001800076Q00A2000800026Q000900016Q000A00026Q000B00036Q000C00046Q000D8Q000E00063Q00202Q000F000600014Q000C000F6Q000B3Q00024Q000C00036Q000D00046Q000E00016Q000F00016Q000F0006000F00102Q000F0001000F4Q001000016Q00100006001000102Q00100001001000202Q0010001000014Q000D00106Q000C8Q000A3Q000200202Q000A000A00024Q0009000A6Q00073Q000100043E0003000500012Q0018000300054Q004C000400024Q007F000300044Q009C00036Q007C3Q00017Q00063Q0003143Q00B2018473F9722EB008826FF27F34AC0C8766F96403073Q0071E24DC52ABC20028Q00030B3Q00426967576967734461746103083Q004D652Q736167657303063Q00536F756E647302124Q003F00025Q00122Q000300013Q00122Q000400026Q00020004000200062Q000100110001000200048A3Q0011000100127A000200033Q0026B6000200070001000300048A3Q000700012Q0018000300013Q00208E00030003000400302Q0003000500034Q000300013Q00202Q00030003000400302Q00030006000300044Q0011000100048A3Q000700012Q007C3Q00017Q00103Q00028Q00026Q00F03F030E3Q005F42696757696773482Q6F6B6564030E3Q00682Q6F6B73656375726566756E63030D3Q00426967576967734C6F61646572030B3Q000913FAB11713E7A63B11F103043Q00D55A76942Q0103083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q00E97E2363F434DBF4542B46F803073Q00A8AB1744349D5303083Q00F974E6BE242A82E703073Q00E7941195CD454D03063Q0093A8D2F553EC03063Q009FE0C7A79B37003B3Q00127A3Q00014Q0015000100033Q0026B63Q001F0001000200048A3Q001F00010006A70001003A00013Q00048A3Q003A00010006A70002003A00013Q00048A3Q003A00012Q001800045Q00204A00040004000300065F0004003A0001000100048A3Q003A000100127A000400013Q0026B60004000D0001000100048A3Q000D0001001207000500043Q001209000600056Q000700013Q00122Q000800063Q00122Q000900076Q0007000900020006AD00083Q000100032Q00183Q00014Q004C3Q00034Q00188Q000B0005000800012Q001800055Q00301B00050003000800048A3Q003A000100048A3Q000D000100048A3Q003A00010026B63Q00020001000100048A3Q00020001001207000400093Q00209900040004000A4Q000500013Q00122Q0006000B3Q00122Q0007000C6Q000500076Q00043Q00054Q000200056Q000100046Q00043Q00024Q000500013Q00122Q0006000D3Q00122Q0007000E6Q0005000700024Q00068Q0004000500064Q000500013Q00122Q0006000F3Q00122Q000700106Q0005000700024Q00068Q0004000500064Q000300043Q00124Q00023Q00044Q000200012Q007C3Q00013Q00013Q002F3Q00028Q00030F3Q007927B361445C3D8B7B2Q483DB5514803053Q002D3B4ED43603053Q007461626C6503063Q00696E7365727403083Q006D652Q736167657303093Q00045F2Q8E953AACFD0003083Q00907036E3EBE64ECD03073Q0047657454696D6503043Q00A72D17E803063Q003BD3486F9CB003053Q004D88EF225C03043Q004D2EE783026Q00F03F03063Q00736F756E647303093Q0074696D657374616D70026Q001040031B3Q00556E697444657461696C6564546872656174536974756174696F6E03063Q00AA58B759BF4603043Q0020DA34D603063Q005A1623AFF4A403083Q003A2E7751C891D02503053Q00736F756E6403053Q002A8031BEA403073Q00564BEC50CCC9DD030B3Q00426967576967734461746103063Q00536F756E647303073Q006540658BF7857503063Q00EB122117E59E027Q0040026Q000840030D3Q0072B3C68C59BDD28463B5D4B55403043Q00DB30DAA103093Q00F078714CC85BE1E96103073Q008084111C29BB2F03053Q00123D13345903053Q003D6152665A03063Q00BC22AA52C24503083Q0069CC4ECB2BA7377E03063Q00B1AB3119161003083Q0031C5CA437E7364A703053Q00636F6C6F7203063Q003849DE27875303073Q003E573BBF49E03603083Q004D652Q736167657303063Q00F717E8D9EB0703043Q00A987629A02CA3Q00127A000300014Q0015000400043Q0026B6000300940001000100048A3Q009400012Q001800055Q00127A000600023Q00127A000700034Q00310005000700020006200001006B0001000500048A3Q006B000100127A000500014Q00150006000A3Q0026B60005002B0001000100048A3Q002B00012Q0097000B000F4Q00720009000E6Q0008000D6Q0007000C6Q0006000B3Q00122Q000B00043Q00202Q000B000B00054Q000C00013Q00202Q000C000C00064Q000D3Q00034Q000E5Q00122Q000F00073Q00122Q001000086Q000E0010000200122Q000F00096Q000F000100024Q000D000E000F4Q000E5Q00122Q000F000A3Q00122Q0010000B6Q000E001000024Q000D000E00084Q000E5Q00122Q000F000C3Q00122Q0010000D6Q000E001000024Q000D000E00094Q000B000D000100122Q0005000E3Q0026B60005000C0001000E00048A3Q000C00012Q0018000B00013Q00205C000B000B000F4Q000C00013Q00202Q000C000C000F4Q000C000C6Q000A000B000C00062Q000A008D00013Q00048A3Q008D0001001207000B00094Q006E000B0001000200204A000C000A00102Q0078000B000B000C00262E000B008D0001001100048A3Q008D000100127A000B00014Q0015000C000D3Q000E510001003D0001000B00048A3Q003D0001001207000E00124Q00BC000F5Q00122Q001000133Q00122Q001100146Q000F001100024Q00105Q00122Q001100153Q00122Q001200166Q001000126Q000E3Q000F4Q000D000F6Q000C000E3Q00202Q000E000A00174Q000F5Q00122Q001000183Q00122Q001100196Q000F0011000200062Q000E00560001000F00048A3Q005600012Q0018000E00023Q00204A000E000E001A00301B000E001B000E00048A3Q008D000100204A000E000A00172Q003F000F5Q00122Q0010001C3Q00122Q0011001D6Q000F0011000200062Q000E008D0001000F00048A3Q008D000100065F000C00630001000100048A3Q00630001002657000D00630001001E00048A3Q006300010026B6000D008D0001001F00048A3Q008D00012Q0018000E00023Q00204A000E000E001A00301B000E001B001E00048A3Q008D000100048A3Q003D000100048A3Q008D000100048A3Q000C000100048A3Q008D00012Q001800055Q00127A000600203Q00127A000700214Q00310005000700020006200001008D0001000500048A3Q008D000100127A000500014Q0015000600083Q0026B6000500730001000100048A3Q007300012Q00970009000C4Q000E0008000B6Q0007000A6Q000600093Q00122Q000900043Q00202Q0009000900054Q000A00013Q00202Q000A000A000F4Q000B3Q00024Q000C5Q00122Q000D00223Q00122Q000E00236Q000C000E000200122Q000D00096Q000D000100024Q000B000C000D4Q000C5Q00122Q000D00243Q00122Q000E00256Q000C000E00024Q000B000C00084Q0009000B000100044Q008D000100048A3Q007300012Q0018000500013Q00202D0005000500064Q000600013Q00202Q0006000600064Q000600066Q00040005000600122Q0003000E3Q0026B6000300020001000E00048A3Q000200010006A7000400C900013Q00048A3Q00C90001001207000500094Q006E00050001000200204A0006000400102Q007800050005000600262E000500C90001001100048A3Q00C9000100127A000500014Q0015000600073Q000E51000100A00001000500048A3Q00A00001001207000800124Q00BC00095Q00122Q000A00263Q00122Q000B00276Q0009000B00024Q000A5Q00122Q000B00283Q00122Q000C00296Q000A000C6Q00083Q00094Q000700096Q000600083Q00202Q00080004002A4Q00095Q00122Q000A002B3Q00122Q000B002C6Q0009000B000200062Q000800B90001000900048A3Q00B900012Q0018000800023Q00204A00080008001A00301B0008002D000E00048A3Q00C9000100204A00080004002A2Q003F00095Q00122Q000A002E3Q00122Q000B002F6Q0009000B000200062Q000800C90001000900048A3Q00C900010006A7000600C900013Q00048A3Q00C900012Q0018000800023Q00204A00080008001A00301B0008002D001E00048A3Q00C9000100048A3Q00A0000100048A3Q00C9000100048A3Q000200012Q007C3Q00017Q000C3Q00028Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q00022BC7541821C15A3E27DA5503043Q003B4A4EB5030C3Q004865726F526F746174696F6E03123Q005F4D794C6567656E64617279482Q6F6B6564030E3Q00682Q6F6B73656375726566756E6303093Q004E616D65706C61746503073Q0004D55E73B02ADF03053Q00D345B12Q3A2Q0100293Q00127A3Q00014Q0015000100023Q0026B63Q00020001000100048A3Q00020001001207000300023Q0020860003000300034Q00045Q00122Q000500043Q00122Q000600056Q000400066Q00033Q00044Q000200046Q000100033Q00062Q0001002800013Q00048A3Q002800010006A70002002800013Q00048A3Q00280001001207000300064Q0018000400013Q00204A00040004000700065F000400280001000100048A3Q0028000100127A000400013Q000E51000100170001000400048A3Q00170001001207000500083Q00206D0006000300094Q00075Q00122Q0008000A3Q00122Q0009000B6Q0007000900020006AD00083Q000100012Q00183Q00014Q000B0005000800012Q0018000500013Q00301B00050007000C00048A3Q0028000100048A3Q0017000100048A3Q0028000100048A3Q000200012Q007C3Q00013Q00013Q00063Q0003063Q00556E6974494403063Q0048724461746103053Q00546F6B656E03063Q00737472696E6703053Q006C6F7765720002113Q0006A73Q000D00013Q00048A3Q000D000100204A00023Q00010006A70002000D00013Q00048A3Q000D00012Q001800025Q00208900020002000200122Q000300043Q00202Q00030003000500202Q00043Q00014Q00030002000200102Q00020003000300044Q001000012Q001800025Q00204A00020002000200301B0002000300062Q007C3Q00017Q000B3Q00028Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q009FE06BFADBC4A3E46DFCE6C503063Q00ABD785199589030C3Q004865726F526F746174696F6E030B3Q005F54657874482Q6F6B6564030E3Q00682Q6F6B73656375726566756E63030D3Q00C2C921EECE3EF24DF5C926FFEB03083Q002281A8529A8F509C2Q0100293Q00127A3Q00014Q0015000100023Q000E510001000200013Q00048A3Q00020001001207000300023Q0020860003000300034Q00045Q00122Q000500043Q00122Q000600056Q000400066Q00033Q00044Q000200046Q000100033Q00062Q0001002800013Q00048A3Q002800010006A70002002800013Q00048A3Q00280001001207000300064Q0018000400013Q00204A00040004000700065F000400280001000100048A3Q0028000100127A000400013Q0026B6000400170001000100048A3Q00170001001207000500084Q009F000600036Q00075Q00122Q000800093Q00122Q0009000A6Q0007000900020006AD00083Q000100012Q00183Q00014Q000B0005000800012Q0018000500013Q00301B00050007000B00048A3Q0028000100048A3Q0017000100048A3Q0028000100048A3Q000200012Q007C3Q00013Q00013Q00023Q0003063Q0048724461746103083Q00436173745465787405044Q001800055Q00204A0005000500010010840005000200022Q007C3Q00017Q00643Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q00E94720D937CE5633C20CCE4C03053Q0065A12252B6030C3Q004865726F526F746174696F6E03073Q004865726F4C696203043Q00556E697403063Q00506C6179657203163Q00476574456E656D696573496E4D656C2Q6552616E6765026Q00244003113Q00476574456E656D696573496E52616E6765026Q00444003063Q0054617267657403173Q00476574456E656D696573496E53706C61736852616E6765028Q0003063Q00487244617461030D3Q00546172676574496E4D656C2Q65030D3Q00546172676574496E52616E6765030E3Q00546172676574496E53706C617368030D3Q004C65667449636F6E4672616D6503093Q00497356697369626C65026Q00F03F030B3Q00435F4E616D65506C61746503133Q004765744E616D65506C617465466F72556E697403113Q006E616D65506C617465556E69744755494403083Q00556E69744755494403093Q00E5024CEDDEED942BFA03083Q004E886D399EBB82E203073Q004379636C654D4F2Q0103093Q004379636C65556E69740100030C3Q004379636C655370652Q6C494403023Q00494403053Q00546F6B656E030D3Q004D61696E49636F6E4672616D65030A3Q004E6F74496E52616E676503073Q005370652Q6C494403073Q0054657874757265030E3Q00476574566572746578436F6C6F72029A5Q99D93F03023Q005F47031B3Q007370652Q6C5479706548656B696C695772612Q706572436163686503203Q007370652Q6C5479706548656B696C695772612Q70657243616368654672616D65030D3Q004C48656B696C6952656349644C030C3Q004C52616E6765436865636B4C03133Q004C4865726F526F746174696F6E52656349644C03063Q00163AF2F8323603043Q00915E5F99030B3Q004372656174654672616D6503053Q00DBFF35F86B03063Q00D79DAD74B52E030D3Q0052656769737465724576656E7403153Q000598AACBFF078BAEDCEE1086A2DCFD0A83A4C0F61103053Q00BA55D4EB9203173Q00EEAE37DA10C07FFDB235CC1CCB76FDA53FCD18CC74E7A503073Q0038A2E1769E598E03093Q0053657453637269707403073Q00730BE5B927D64803063Q00B83C65A0CF4203083Q0048656B696C69444203083Q0070726F66696C657303073Q0044656661756C7403073Q00746F2Q676C657303043Q006D6F646503053Q0076616C756503083Q00564FCF76244D5CCB03053Q0050242AAE1503043Q004A05367603043Q001A2E7057024Q00ECDD1541024Q006056F340024Q007092FA40024Q0084131741025Q0097F34003073Q00435F5370652Q6C03103Q004765745370652Q6C432Q6F6C646F776E025Q00EFED4003093Q00737461727454696D6503083Q006475726174696F6E03083Q00746F6E756D62657203073Q004765744356617203103Q006B07224A542632434D12104F5613285103043Q0026387747030B3Q004765744E65745374617473026Q006440030F3Q00556E697443617374696E67496E666F03063Q002QE359CF204403063Q0036938F38B645030F3Q00556E69744368612Q6E656C496E666F03063Q00C68DFE50DAC403053Q00BFB6E19F2903073Q005072696D6172792Q033Q00414F4503103Q00DDE7A73CE2C6B735FBF29539E0F3AD2703043Q00508E97C203063Q0013CA765506D403043Q002C63A61703063Q006CFB282F36B603063Q00C41C97495653020C023Q008700028Q0002000100014Q000200016Q0002000100014Q000200026Q00020001000100122Q000200013Q00202Q0002000200024Q000300033Q00122Q000400033Q00122Q000500046Q000300056Q00023Q000300062Q000200F500013Q00048A3Q00F500010006A7000300F500013Q00048A3Q00F50001001207000400053Q00120F000500063Q00202Q00060005000700202Q00060006000800202Q00060006000900122Q0008000A6Q00060008000200202Q00070005000700202Q00070007000800202Q00070007000B00122Q0009000C6Q00070009000200202Q00080005000700202Q00080008000D00202Q00080008000E00122Q000A000A6Q0008000A00024Q000900063Q000E2Q000F00290001000900048A3Q002900012Q0018000900043Q00204A0009000900102Q0032000A00063Q00108400090011000A2Q0032000900073Q000E47000F00300001000900048A3Q003000012Q0018000900043Q00204A0009000900102Q0032000A00073Q00108400090012000A2Q0032000900083Q000E47000F00370001000900048A3Q003700012Q0018000900043Q00204A0009000900102Q0032000A00083Q00108400090013000A00204A0009000400140006A7000900A100013Q00048A3Q00A1000100204A00090004001400202C0009000900152Q00C50009000200020006A7000900A100013Q00048A3Q00A1000100127A0009000F4Q0015000A000A3Q0026B6000900940001001600048A3Q009400010006A7000A008800013Q00048A3Q0088000100127A000B000F4Q0015000C000C3Q0026B6000B00470001000F00048A3Q00470001001207000D00173Q0020A5000D000D00184Q000E000A6Q000D000200024Q000C000D3Q00062Q000C007A00013Q00048A3Q007A000100204A000D000C00190006A7000D007A00013Q00048A3Q007A000100127A000D000F4Q0015000E000E3Q0026B6000D00550001000F00048A3Q0055000100204A000E000C0019001240000F001A6Q001000033Q00122Q0011001B3Q00122Q0012001C6Q001000126Q000F3Q000200062Q000F006C0001000E00048A3Q006C000100127A000F000F3Q000E51000F00610001000F00048A3Q006100012Q0018001000043Q00208E00100010001000302Q0010001D001E4Q001000043Q00202Q00100010001000302Q0010001F002000044Q00B2000100048A3Q0061000100048A3Q00B2000100127A000F000F3Q000E51000F006D0001000F00048A3Q006D00012Q0018001000043Q00208E00100010001000302Q0010001D00204Q001000043Q00202Q00100010001000302Q0010001F001E00044Q00B2000100048A3Q006D000100048A3Q00B2000100048A3Q0055000100048A3Q00B2000100127A000D000F3Q0026B6000D007B0001000F00048A3Q007B00012Q0018000E00043Q00208E000E000E001000302Q000E001D00204Q000E00043Q00202Q000E000E001000302Q000E001F002000044Q00B2000100048A3Q007B000100048A3Q00B2000100048A3Q0047000100048A3Q00B2000100127A000B000F3Q0026B6000B00890001000F00048A3Q008900012Q0018000C00043Q00208E000C000C001000302Q000C001D00204Q000C00043Q00202Q000C000C001000302Q000C001F002000044Q00B2000100048A3Q0089000100048A3Q00B200010026B6000900410001000F00048A3Q004100012Q0018000B00043Q002061000B000B001000202Q000C0004001400202Q000C000C002200102Q000B0021000C4Q000B00043Q00202Q000B000B001000202Q000A000B002300122Q000900163Q00044Q0041000100048A3Q00B2000100127A0009000F3Q0026B6000900A80001001600048A3Q00A800012Q0018000A00043Q00204A000A000A001000301B000A001F002000048A3Q00B200010026B6000900A20001000F00048A3Q00A200012Q0018000A00043Q0020A0000A000A001000302Q000A0021000F4Q000A00043Q00202Q000A000A001000302Q000A001D002000122Q000900163Q00044Q00A2000100204A0009000400240006A7000900EA00013Q00048A3Q00EA000100204A00090004002400202C0009000900152Q00C50009000200020006A7000900EA00013Q00048A3Q00EA000100127A0009000F4Q0015000A000C3Q0026B6000900D10001001600048A3Q00D1000100204A000D0004002400204A000D000D00220006A7000D00CD00013Q00048A3Q00CD00012Q0018000D00043Q00204A000D000D001000204A000D000D002500065F000D00CD0001000100048A3Q00CD00012Q0018000D00043Q00204E000D000D001000202Q000E0004002400202Q000E000E002200102Q000D0026000E00044Q00F500012Q0018000D00043Q00204A000D000D001000301B000D0026000F00048A3Q00F500010026B6000900BC0001000F00048A3Q00BC000100204A000D00040024002059000D000D002700202Q000D000D00284Q000D0002000F4Q000C000F6Q000B000E6Q000A000D3Q00262Q000B00E40001001600048A3Q00E40001000E47002900E40001000B00048A3Q00E40001002616000C00E40001001600048A3Q00E400012Q0018000D00043Q00204A000D000D001000301B000D0025001E00048A3Q00E700012Q0018000D00043Q00204A000D000D001000301B000D0025002000127A000900163Q00048A3Q00BC000100048A3Q00F5000100127A0009000F3Q000E51000F00EB0001000900048A3Q00EB00012Q0018000A00043Q00208E000A000A001000302Q000A0026000F4Q000A00043Q00202Q000A000A001000302Q000A0025002000044Q00F5000100048A3Q00EB00010012070004002A3Q0012070005002A3Q00204A00050005002B00065F000500FB0001000100048A3Q00FB00012Q001000055Q0010840004002B00050012070004002A3Q0012070005002A3Q00204A00050005002C00065F000500022Q01000100048A3Q00022Q012Q001000055Q0010840004002C00050012070004002A3Q0012070005002A3Q00204A00050005002D00065F000500092Q01000100048A3Q00092Q012Q001000055Q0010840004002D00050012070004002A3Q0012070005002A3Q00204A00050005002E00065F000500102Q01000100048A3Q00102Q012Q001000055Q0010840004002E00050012070004002A3Q0012070005002A3Q00204A00050005002F00065F000500172Q01000100048A3Q00172Q012Q001000055Q0010840004002F00050012AA000400013Q00202Q0004000400024Q000500033Q00122Q000600303Q00122Q000700316Q000500076Q00043Q000500122Q0006002A3Q00202Q00060006002C00062Q0006004D2Q01000100048A3Q004D2Q0100127A0006000F3Q0026B6000600372Q01000F00048A3Q00372Q010012070007002A3Q00123D000800326Q000900033Q00122Q000A00333Q00122Q000B00346Q0009000B6Q00083Q000200102Q0007002C000800122Q0007002A3Q00202Q00070007002C00202Q0007000700354Q000900033Q00122Q000A00363Q00122Q000B00376Q0009000B6Q00073Q000100122Q000600163Q0026B6000600242Q01001600048A3Q00242Q010012070007002A3Q00204200070007002C00202Q0007000700354Q000900033Q00122Q000A00383Q00122Q000B00396Q0009000B6Q00073Q000100122Q0007002A3Q00202Q00070007002C00202Q00070007003A4Q000900033Q00122Q000A003B3Q00122Q000B003C6Q0009000B00020006AD000A3Q000100012Q00183Q00034Q000B0007000A000100048A3Q004D2Q0100048A3Q00242Q012Q0003000600013Q0006A7000400B92Q013Q00048A3Q00B92Q010006A7000500B92Q013Q00048A3Q00B92Q010012070007003D3Q00206000070007003E00202Q00070007003F00202Q00070007004000202Q00070007004100202Q0007000700424Q00088Q000900033Q00122Q000A00433Q00122Q000B00446Q0009000B000200062Q000700652Q01000900048A3Q00652Q012Q0018000900033Q00127A000A00453Q00127A000B00464Q00310009000B0002000620000700662Q01000900048A3Q00662Q012Q0003000800014Q001000093Q000400300C00090047001E00302Q00090048001E00302Q00090049001E00302Q0009004A001E4Q000A3Q000100302Q000A004B001E0006AD000B0001000100012Q004C3Q00093Q0006AD000C0002000100012Q004C3Q000A3Q0006AD000D0003000100012Q00183Q00033Q000256000E00043Q000256000F00053Q000256001000063Q000256001100073Q0012930012004C3Q00202Q00120012004D00122Q0013004E6Q00120002000200202Q00130012004F00202Q00140012005000122Q001500513Q00122Q001600526Q001700033Q00122Q001800533Q00122Q001900546Q001700196Q00168Q00153Q000200122Q001600556Q00160001001900202Q001A0019005600122Q001B00576Q001C00033Q00122Q001D00583Q00122Q001E00596Q001C001E6Q001B3Q002300122Q0024005A6Q002500033Q00122Q0026005B3Q00122Q0027005C6Q002500276Q00243Q002B0006AD002C00080001000F2Q00183Q00034Q004C3Q00084Q004C3Q00104Q004C3Q000C4Q004C3Q00114Q004C3Q00144Q004C3Q001A4Q00183Q00044Q004C3Q000E4Q004C3Q001F4Q004C3Q000F4Q004C3Q00284Q004C3Q00064Q004C3Q000B4Q004C3Q000D4Q006B002D002C6Q002D0001000200202Q002E002D005D00202Q002F002D005E00122Q0030002A3Q00202Q00300030002D00062Q003000B72Q013Q00048A3Q00B72Q0100127A0030000F3Q0026B6003000AD2Q01000F00048A3Q00AD2Q010012070031002A3Q00208100310031002D00102Q0031005D002E00122Q0031002A3Q00202Q00310031002D00102Q0031005E002F00044Q00B72Q0100048A3Q00AD2Q012Q002200075Q00048A3Q00C82Q010012070007002A3Q00204A00070007002D0006A7000700C82Q013Q00048A3Q00C82Q0100127A0007000F3Q0026B6000700BE2Q01000F00048A3Q00BE2Q010012070008002A3Q00209D00080008002D00302Q0008005D000F00122Q0008002A3Q00202Q00080008002D00302Q0008005E000F00044Q00C82Q0100048A3Q00BE2Q010006A70002000402013Q00048A3Q000402010006A70003000402013Q00048A3Q00040201000256000700093Q0002560008000A3Q0002560009000B3Q000256000A000C3Q001293000B004C3Q00202Q000B000B004D00122Q000C004E6Q000B0002000200202Q000C000B004F00202Q000D000B005000122Q000E00513Q00122Q000F00526Q001000033Q00122Q0011005F3Q00122Q001200606Q001000126Q000F8Q000E3Q000200122Q000F00556Q000F0001001200202Q00130012005600122Q001400576Q001500033Q00122Q001600613Q00122Q001700626Q001500176Q00143Q001C00122Q001D005A6Q001E00033Q00122Q001F00633Q00122Q002000646Q001E00206Q001D3Q00240006AD0025000D0001000A2Q00183Q00044Q00183Q00034Q004C3Q00094Q004C3Q000A4Q004C3Q000D4Q004C3Q00134Q004C3Q00074Q004C3Q00184Q004C3Q00084Q004C3Q00214Q0038002600256Q00260001000200202Q00270026005D00122Q0028002A3Q00202Q00280028002F00062Q0028002Q02013Q00048A3Q002Q02010012070028002A3Q00204A00280028002F0010840028002600272Q002200075Q00048A3Q000B02010012070007002A3Q00204A00070007002F0006A70007000B02013Q00048A3Q000B02010012070007002A3Q00204A00070007002F00301B00070026000F2Q007C3Q00013Q000E3Q000D3Q0003153Q0001AE5D8514B043991FB6598E18AC5B8306AD4E901503043Q00DC51E21C03173Q003FFAA3DFC3E934EAB12QD8E236FBBDDFC3F432F7AEDECE03063Q00A773B5E29B8A028Q00026Q00F03F03053Q007072696E74033A3Q00D027F4596F65CFEC25A7547E7ACFEE2BA74B6970D6F227F51C7870C5EA27A7537531C3EC36E24E727FC1A223A7527E6686EB2CF4487A7FC5E76C03073Q00A68242873C1B1103023Q005F4703123Q006244616D6167655370652Q6C734361636865031B3Q007370652Q6C5479706548656B696C695772612Q70657243616368650002204Q007300035Q00122Q000400013Q00122Q000500026Q00030005000200062Q0001000C0001000300048A3Q000C00012Q001800035Q00127A000400033Q00127A000500044Q00310003000500020006200001001F0001000300048A3Q001F000100127A000300053Q0026B6000300160001000600048A3Q00160001001207000400074Q003300055Q00122Q000600083Q00122Q000700096Q000500076Q00043Q000100044Q001F00010026B60003000D0001000500048A3Q000D00010012070004000A4Q00B300055Q00102Q0004000B000500122Q0004000A3Q00302Q0004000C000D00122Q000300063Q00044Q000D00012Q007C3Q00017Q00043Q00028Q0003053Q007061697273030B3Q00435F556E6974417572617303163Q00476574506C617965724175726142795370652Q6C4944001C3Q00127A3Q00013Q000E510001000100013Q00048A3Q00010001001207000100024Q001800026Q002700010002000300048A3Q0016000100127A000600014Q0015000700073Q0026B6000600090001000100048A3Q00090001001207000800033Q0020A50008000800044Q000900046Q0008000200024Q000700083Q00062Q0007001600013Q00048A3Q001600012Q0003000800014Q0005000800023Q00048A3Q0016000100048A3Q000900010006A9000100070001000200048A3Q000700012Q000300016Q0005000100023Q00048A3Q000100012Q007C3Q00017Q00023Q00028Q0003053Q00706169727301113Q00127A000100013Q0026B6000100010001000100048A3Q00010001001207000200024Q001800036Q002700020002000400048A3Q000B00010006200005000B00013Q00048A3Q000B00012Q000300076Q0005000700023Q0006A9000200070001000200048A3Q000700012Q0003000200014Q0005000200023Q00048A3Q000100012Q007C3Q00017Q00653Q0003023Q005F47031B3Q007370652Q6C5479706548656B696C695772612Q7065724361636865030D3Q006973496E697469616C697A65642Q0103063Q00756E7061636B030B3Q004372656174654672616D65030B3Q009E22A6718BB04AB8AD2ABB03083Q00D4D943CB142QDF2503133Q009D8CA5D78E82A7DEAE84B8E6BF80B8DEBB99AD03043Q00B2DAEDC803083Q005365744F776E657203083Q005549506172656E74030B3Q00979BC5F89987D9FE999BC303043Q00B0D6D586030C3Q005365745370652Q6C4279494403083Q004E756D4C696E6573026Q00F03F03073Q004765744E616D6503083Q00C0A8AEC084535FE003073Q003994CDD6B4C83603073Q004765745465787403063Q00737472696E6703053Q006C6F77657203043Q0066696E6403073Q001BF32620771CE903053Q0016729D555403063Q00D7C415CB4FE203073Q00C8A4AB73A43D9603083Q00B7FA105182B0E00603053Q00E3DE946325030C3Q00696E7374616E74616EC3A965030A3Q003A41462QF727535CF3F603053Q0099532Q3296030C3Q00696E7374616E74C3A26E656F03253Q00D0BCD0B3D0BDD0BED0B2D0B5D0BDD0BDD0BED0B520D0B4D0B5D0B9D181D182D0B2D0B8D0B503063Q00ECA689EC8B9C03063Q00E79EACE58F9103153Q005E77600872A941583664147AA7481D7B7C0A7AA54A03073Q002D3D16137C13CB032B3Q00CA1303FB4271ACD25209F01030BBC40508F2177EBE811A08E70365AA811508E20B62B2D5521AF01074BCCF03073Q00D9A1726D956210031D3Q000125786CA97116257870BD7A08212A3CB97A522D376AB5791B253668B303063Q00147240581CDC032A3Q007065757420C3AA747265206C616E63C3A920656E20636F7572732064652064C3A9706C6163656D656E7403173Q003D00DCB7F1D1BF380DD7F4F1DEFD3C0EC4BDF5D5B3250E03073Q00DD5161B2D498B003213Q00C3A920706F2Q73C3AD76656C206C616EC3A7617220656D206D6F76696D656E746F032B3Q00D0BCD0BED0B6D0BDD0BE20D0BFD180D0B8D0BCD0B5D0BDD18FD182D18C20D0BDD0B020D185D0BED0B4D18303283Q00EC9DB4EB8F9920ECA491EC979020EC8B9CECA084ED95A020EC889820EC9E88EC8AB5EB8B88EB8BA403183Q00E58FAFE4BBA5E59CA8E7A7BBE58AA8E4B8ADE696BDE694BE03133Q00D8F41CF916C8A70AF313C1E25DF615DBEE13FC03053Q007AAD877D9B03223Q0085D413F93B34DAC4C305AE3A36DD8AC640B13A23C991D240BC363FDB81D51ABB3E2303073Q00A8E4A160D95F51031F3Q00C8D46E4C3A52DFD46E493B5ED7D8345D3D17DEDF6E512041D2DC27592143D403063Q0037BBB14E3C4F03233Q007574696C697361626C6520656E20636F7572732064652064C3A9706C6163656D656E7403193Q0038DA56E74FD59A2CCC56E7438F89238E52E450C68D28C04BE403073Q00E04DAE3F8B26AF031B3Q00944E5C2BC4525D3CC4544B2F804E182B890155219248552B8A555703043Q004EE4213803283Q00EC9DB4EB8F9920ECA491EC979020EC82ACEC9AA9ED95A020EC889820EC9E88EC8AB5EB8B88EB8BA403153Q00E58FAFE59CA8E7A7BBE58AA8E4B8ADE696BDE694BE03163Q00CD76B30D8BCB72B707C5D976BB0F808E73BD158CC07903053Q00E5AE1ED263032F3Q0010EC885FAD3C2C08AD8254FF7D3B1EFA8356F8333E5BE58343EC282A5BE6875FEC313008E48343F97D2E1EFF8254E303073Q00597B8DE6318D5D031F3Q00E364F308150AF070F80D1C43E970E41F150AF67FB6011F5CFA7CFF091E5EFC03063Q002A9311966C7003263Q007065757420C3AA7472652063616E616C6973C3A920656E2073652064C3A9706C61C3A7616E7403193Q001AB22473EEF215A72F76EBED4FAF233FEAE719AF207AE9FC0003063Q00886FC64D1F8703203Q001206A353FDF712BB420AA658BCE81EB3030DA816B8E957A40D1FAE5BB8EA03A603083Q00C96269C736DD847703373Q00D0BCD0BED0B6D0BDD0BE20D0BFD0BED0B4D0B4D0B5D180D0B6D0B8D0B2D0B0D182D18C20D0B220D0B4D0B2D0B8D0B6D0B5D0BDD0B8D0B803183Q00E58FAFE4BBA5E59CA8E7A7BBE58AA8E4B8ADE5BC95E5AFBC03073Q00BA04822F0C30A003073Q00CCD96CE3416255030C3Q0055C2FBE420C94DCAF0F729CE03063Q00A03EA395854C03093Q00D5A1032ECFDFBA0C2103053Q00A3B6C06D4F030A3Q0037270EC1F93D3505CEE103053Q0095544660A0030B3Q003B0703EC340F17F739080203043Q008D58666D03093Q00B052C47116344FC0BE03083Q00A1D333AA107A5D35032D3Q00D0BFD0BED0B4D0B4D0B5D180D0B6D0B8D0B2D0B0D18ED18220D0B7D0B0D0BAD0BBD0B8D0BDD0B0D0BDD0B8D0B503063Q00ECB184EB849003063Q00E6B5B7E5B3A103053Q006D6174636803173Q00B3EBB663BEE0ED6DFFE4FB68E8ABB168FEA3A227ECABA003043Q00489BCED20100028Q00024Q00A0CAF84003063Q0069706169727303043Q0048696465030D3Q004F697D003A527355023A5C7F5003053Q0053261A346E0207022Q001207000200013Q00204A0002000200022Q0058000200023Q0006A70002000C00013Q00048A3Q000C000100204A0003000200030026B60003000C0001000400048A3Q000C0001001207000300054Q004C000400024Q007F000300044Q009C00035Q001207000300064Q00B900045Q00122Q000500073Q00122Q000600086Q0004000600024Q000500016Q000600066Q00075Q00122Q000800093Q00122Q0009000A6Q000700096Q00033Q000200202Q00040003000B00122Q0006000C6Q00075Q00122Q0008000D3Q00122Q0009000E6Q000700096Q00043Q000100202Q00040003000F4Q00068Q0004000600014Q000400016Q00058Q00068Q00078Q00085Q00202Q0009000300104Q00090002000200122Q000A00116Q000B00093Q00122Q000C00113Q00042Q000A00DA2Q01001207000E00013Q0020AB000F000300124Q000F000200024Q00105Q00122Q001100133Q00122Q001200146Q0010001200024Q0011000D6Q000F000F00114Q000E000E000F00062Q000E00D92Q013Q00048A3Q00D92Q0100202C000F000E00152Q00C5000F000200020006A7000F00D92Q013Q00048A3Q00D92Q01001207001000163Q0020250010001000174Q0011000F6Q00100002000200122Q001100163Q00202Q0011001100184Q001200106Q00135Q00122Q001400193Q00122Q0015001A6Q001300156Q00113Q000200062Q0011008C0001000100048A3Q008C0001001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q0014001B3Q00122Q0015001C6Q001300156Q00113Q000200062Q0011008C0001000100048A3Q008C0001001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q0014001D3Q00122Q0015001E6Q001300156Q00113Q000200062Q0011008C0001000100048A3Q008C0001001207001100163Q0020A30011001100184Q001200103Q00122Q0013001F6Q00110013000200062Q0011008C0001000100048A3Q008C0001001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400203Q00122Q001500216Q001300156Q00113Q000200062Q0011008C0001000100048A3Q008C0001001207001100163Q0020A30011001100184Q001200103Q00122Q001300226Q00110013000200062Q0011008C0001000100048A3Q008C0001001207001100163Q0020A30011001100184Q001200103Q00122Q001300236Q00110013000200062Q0011008C0001000100048A3Q008C0001001207001100163Q0020A30011001100184Q001200103Q00122Q001300246Q00110013000200062Q0011008C0001000100048A3Q008C0001001207001100163Q0020B40011001100184Q001200103Q00122Q001300256Q00110013000200062Q0011008E00013Q00048A3Q008E00012Q0003000500013Q00048A3Q00D92Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400263Q00122Q001500276Q001300156Q00113Q000200062Q001100D90001000100048A3Q00D90001001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400283Q00122Q001500296Q001300156Q00113Q000200062Q001100D90001000100048A3Q00D90001001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q0014002A3Q00122Q0015002B6Q001300156Q00113Q000200062Q001100D90001000100048A3Q00D90001001207001100163Q0020A30011001100184Q001200103Q00122Q0013002C6Q00110013000200062Q001100D90001000100048A3Q00D90001001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q0014002D3Q00122Q0015002E6Q001300156Q00113Q000200062Q001100D90001000100048A3Q00D90001001207001100163Q0020A30011001100184Q001200103Q00122Q0013002F6Q00110013000200062Q001100D90001000100048A3Q00D90001001207001100163Q0020A30011001100184Q001200103Q00122Q001300306Q00110013000200062Q001100D90001000100048A3Q00D90001001207001100163Q0020A30011001100184Q001200103Q00122Q001300316Q00110013000200062Q001100D90001000100048A3Q00D90001001207001100163Q0020B40011001100184Q001200103Q00122Q001300326Q00110013000200062Q001100DB00013Q00048A3Q00DB00012Q0003000800013Q00048A3Q00D92Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400333Q00122Q001500346Q001300156Q00113Q000200062Q001100292Q01000100048A3Q00292Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400353Q00122Q001500366Q001300156Q00113Q000200062Q001100292Q01000100048A3Q00292Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400373Q00122Q001500386Q001300156Q00113Q000200062Q001100292Q01000100048A3Q00292Q01001207001100163Q0020A30011001100184Q001200103Q00122Q001300396Q00110013000200062Q001100292Q01000100048A3Q00292Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q0014003A3Q00122Q0015003B6Q001300156Q00113Q000200062Q001100292Q01000100048A3Q00292Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q0014003C3Q00122Q0015003D6Q001300156Q00113Q000200062Q001100292Q01000100048A3Q00292Q01001207001100163Q0020A30011001100184Q001200103Q00122Q001300306Q00110013000200062Q001100292Q01000100048A3Q00292Q01001207001100163Q0020A30011001100184Q001200103Q00122Q0013003E6Q00110013000200062Q001100292Q01000100048A3Q00292Q01001207001100163Q0020B40011001100184Q001200103Q00122Q0013003F6Q00110013000200062Q0011002B2Q013Q00048A3Q002B2Q012Q0003000800013Q00048A3Q00D92Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400403Q00122Q001500416Q001300156Q00113Q000200062Q001100792Q01000100048A3Q00792Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400423Q00122Q001500436Q001300156Q00113Q000200062Q001100792Q01000100048A3Q00792Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400443Q00122Q001500456Q001300156Q00113Q000200062Q001100792Q01000100048A3Q00792Q01001207001100163Q0020A30011001100184Q001200103Q00122Q001300466Q00110013000200062Q001100792Q01000100048A3Q00792Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400473Q00122Q001500486Q001300156Q00113Q000200062Q001100792Q01000100048A3Q00792Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400493Q00122Q0015004A6Q001300156Q00113Q000200062Q001100792Q01000100048A3Q00792Q01001207001100163Q0020A30011001100184Q001200103Q00122Q0013004B6Q00110013000200062Q001100792Q01000100048A3Q00792Q01001207001100163Q0020A30011001100184Q001200103Q00122Q0013003E6Q00110013000200062Q001100792Q01000100048A3Q00792Q01001207001100163Q0020B40011001100184Q001200103Q00122Q0013004C6Q00110013000200062Q0011007B2Q013Q00048A3Q007B2Q012Q0003000800013Q00048A3Q00D92Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q0014004D3Q00122Q0015004E6Q001300156Q00113Q000200062Q001100CC2Q01000100048A3Q00CC2Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q0014004F3Q00122Q001500506Q001300156Q00113Q000200062Q001100CC2Q01000100048A3Q00CC2Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400513Q00122Q001500526Q001300156Q00113Q000200062Q001100CC2Q01000100048A3Q00CC2Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400533Q00122Q001500546Q001300156Q00113Q000200062Q001100CC2Q01000100048A3Q00CC2Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400553Q00122Q001500566Q001300156Q00113Q000200062Q001100CC2Q01000100048A3Q00CC2Q01001207001100163Q00203B0011001100184Q001200106Q00135Q00122Q001400573Q00122Q001500586Q001300156Q00113Q000200062Q001100CC2Q01000100048A3Q00CC2Q01001207001100163Q0020A30011001100184Q001200103Q00122Q001300596Q00110013000200062Q001100CC2Q01000100048A3Q00CC2Q01001207001100163Q0020A30011001100184Q001200103Q00122Q0013005A6Q00110013000200062Q001100CC2Q01000100048A3Q00CC2Q01001207001100163Q0020B40011001100184Q001200103Q00122Q0013005B6Q00110013000200062Q001100CE2Q013Q00048A3Q00CE2Q012Q0003000600013Q00048A3Q00D92Q01001207001100163Q00209B00110011005C4Q001200106Q00135Q00122Q0014005D3Q00122Q0015005E6Q001300156Q00113Q000200062Q001100D92Q013Q00048A3Q00D92Q012Q0003000700013Q00043E000A002D00010026B6000800F02Q01005F00048A3Q00F02Q0100127A000A00604Q0015000B000B3Q0026B6000A00DE2Q01006000048A3Q00DE2Q012Q0010000C00013Q00127A000D00614Q0088000C000100012Q004C000B000C3Q001207000C00624Q004C000D000B4Q0027000C0002000E00048A3Q00EC2Q01000620001000EC2Q013Q00048A3Q00EC2Q012Q0003000800013Q00048A3Q00F02Q010006A9000C00E82Q01000200048A3Q00E82Q0100048A3Q00F02Q0100048A3Q00DE2Q0100202C000A000300632Q0098000A000200014Q000300033Q00122Q000A00013Q00202Q000A000A00024Q000B000400014Q000C00056Q000D00066Q000E00076Q000F00086Q00105Q00122Q001100643Q00122Q001200656Q0010001200024Q000B001000044Q000B000400012Q0053000A3Q000B2Q0023000A00056Q000B00066Q000C00076Q000D00086Q000A00038Q00017Q00033Q00028Q0003073Q0047657454696D65025Q00408F40010E3Q00127A000100013Q0026B6000100010001000100048A3Q000100010006A73Q000A00013Q00048A3Q000A0001001207000200024Q006E0002000100020020010002000200032Q007800023Q00022Q0005000200024Q0015000200024Q0005000200023Q00048A3Q000100012Q007C3Q00017Q00033Q00028Q0003073Q0047657454696D65025Q00408F40010E3Q00127A000100013Q0026B6000100010001000100048A3Q000100010006A73Q000A00013Q00048A3Q000A0001001207000200024Q006E0002000100020020010002000200032Q007800023Q00022Q0005000200024Q0015000200024Q0005000200023Q00048A3Q000100012Q007C3Q00017Q00083Q00028Q0003073Q00435F5370652Q6C03103Q004765745370652Q6C432Q6F6C646F776E0003093Q00737461727454696D6503083Q006475726174696F6E03073Q0047657454696D65025Q00408F40011B3Q00127A000100014Q0015000200023Q0026B6000100020001000100048A3Q00020001001207000300023Q0020020003000300034Q00048Q0003000200024Q000200033Q00262Q000200170001000400048A3Q0017000100204A000300020005002657000300170001000400048A3Q0017000100204A000300020006001229000400076Q00040001000200202Q0005000200054Q0004000400054Q00030003000400202Q00030003000800062Q000300180001000100048A3Q0018000100127A000300014Q0005000300023Q00048A3Q000200012Q007C3Q00017Q00053Q00028Q0003063Q00435F4974656D030F3Q004765744974656D432Q6F6C646F776E03073Q0047657454696D65025Q00408F4001183Q00127A000100014Q0015000200043Q0026B6000100020001000100048A3Q00020001001207000500023Q0020110005000500034Q00068Q0005000200074Q000400076Q000300066Q000200053Q00262Q000200140001000100048A3Q00140001001207000500044Q00900005000100024Q0005000500024Q00050003000500202Q00050005000500062Q000500150001000100048A3Q0015000100127A000500014Q0005000500023Q00048A3Q000200012Q007C3Q00017Q00133Q0003073Q001B0021588A95DB03073Q00A24B724835EBE703063Q0048656B696C69030B3Q00446973706C6179502Q6F6C03073Q005072696D617279030F3Q005265636F2Q6D656E646174696F6E732Q033Q00AD136103063Q0062EC5C2482332Q033Q00414F4503073Q00940B05B744BAAC03083Q0050C4796CDA25C8D503083Q006E756D49636F6E732Q033Q00215C2703073Q00EA6013621F2B6E028Q0003073Q00360D5BCAAD609203073Q00EB667F32A7CC122Q033Q00718ED003063Q004E30C1954324005B4Q00445Q00024Q00015Q00122Q000200013Q00122Q000300026Q00010003000200122Q000200033Q00202Q00020002000400202Q00020002000500202Q0002000200066Q000100024Q00015Q00122Q000200073Q00122Q000300086Q0001000300024Q000200013Q00062Q0002001700013Q00048A3Q00170001001207000200033Q00204A00020002000400204A00020002000900204A00020002000600065F000200180001000100048A3Q001800012Q0015000200024Q00533Q000100022Q004400013Q00024Q00025Q00122Q0003000A3Q00122Q0004000B6Q00020004000200122Q000300033Q00202Q00030003000400202Q00030003000500202Q00030003000C4Q0001000200034Q00025Q00122Q0003000D3Q00122Q0004000E6Q0002000400024Q000300013Q00062Q0003003000013Q00048A3Q00300001001207000300033Q00204A00030003000400204A00030003000900204A00030003000C00065F000300310001000100048A3Q0031000100127A0003000F4Q00530001000200032Q008500023Q00024Q00035Q00122Q000400103Q00122Q000500116Q00030005000200202Q00020003000F4Q00035Q00122Q000400123Q00122Q000500136Q00030005000200202Q00020003000F0006AD00033Q0001000E2Q00183Q00024Q00183Q00034Q00183Q00044Q00183Q00054Q00183Q00064Q00188Q00183Q00074Q00183Q00084Q00183Q00094Q00183Q000A4Q00183Q000B4Q00183Q000C4Q00183Q000D4Q00183Q000E4Q00B1000400033Q00202Q00053Q000500202Q0006000100054Q00040006000200102Q0002000500044Q000400013Q00062Q0004005900013Q00048A3Q005900012Q004C000400033Q00204A00053Q000900204A0006000100092Q00310004000600020010840002000900042Q0005000200024Q007C3Q00013Q00013Q00403Q00026Q00F03F03083Q00616374696F6E4944028Q00027Q0040030E3Q004973506C617965724D6F76696E67023Q00402244634103063Q0048656B696C6903053Q00436C612Q7303093Q006162696C697469657303043Q006974656D03143Q00476574496E76656E746F72794974656D4C696E6B03063Q0020128101442203053Q0021507EE078026Q002A4003063Q00FCA402DD59FE03053Q003C8CC863A4026Q002C4003063Q0097F8053FA79503053Q00C2E7946446026Q00304003063Q005640C0BAF3DA03063Q00A8262CA1C396026Q00314003063Q0090F0836F35FA03083Q0076E09CE2165088D6026Q002E4003063Q0052E2589947FC03043Q00E0228E39026Q002440026Q001040026Q000840026Q001840026Q001C4003063Q00435F4974656D03123Q004765744974656D496E666F496E7374616E7403023Q00444203073Q0070726F66696C6503073Q00746F2Q676C657303073Q00706F74696F6E7303053Q0076616C756503083Q0053652Q74696E6773030D3Q00FA97F6ED7CE55401D089C4D07603083Q006EBEC7A5BD13913D030C3Q004765744974656D436F756E7403043Q006D6174682Q033Q00616273026Q00144003063Q0073656C656374030B3Q004765744974656D496E666F03073Q00435F5370652Q6C030D3Q0049735370652Q6C557361626C650003043Q0077616974025Q00408F4003093Q00696E64696361746F7203053Q00D9F274E48E03063Q00A7BA8B1788EB03053Q00537461746503083Q0073652Q74696E677303043Q007370656303053Q006379636C652Q01030D3Q0032B08304162QBC0215B99C040A03043Q006D7AD5E80276012Q00127A000200014Q004C000300013Q00127A000400013Q0004A1000200752Q010006A73Q000900013Q00048A3Q000900012Q005800063Q000500065F0006000A0001000100048A3Q000A00012Q0015000600063Q0006A7000600742Q013Q00048A3Q00742Q0100204A0007000600020006A7000700742Q013Q00048A3Q00742Q0100127A000700034Q0015000800103Q0026B6000700462Q01000400048A3Q00462Q01001207001100054Q00A40011000100024Q000F00116Q00118Q001200086Q0011000200024Q001000113Q00062Q000A002400013Q00048A3Q002400012Q0018001100014Q004C001200084Q00C50011000200020006A70011002400013Q00048A3Q0024000100127A001100064Q0005001100023Q00048A3Q00442Q010026160008000F2Q01000300048A3Q000F2Q01001207001100073Q00204A00110011000800204A0011001100092Q00580011001100080006A7001100C800013Q00048A3Q00C8000100204A00120011000A0006A7001200C800013Q00048A3Q00C800012Q0018001200023Q00204A00130011000A2Q00C500120002000200262E001200C80001000100048A3Q00C800012Q0018001200034Q00780012001000122Q0018001300043Q000677001200C80001001300048A3Q00C8000100127A001200034Q00150013001F3Q0026B6001200560001000300048A3Q005600010012070020000B4Q0034002100053Q00122Q0022000C3Q00122Q0023000D6Q00210023000200122Q0022000E6Q0020002200024Q001300203Q00122Q0020000B6Q002100053Q00122Q0022000F3Q00122Q002300106Q00210023000200122Q002200116Q0020002200024Q001400203Q00122Q0020000B6Q002100053Q00122Q002200123Q00122Q002300136Q00210023000200122Q002200146Q0020002200024Q001500203Q00122Q001200013Q0026B6001200710001000100048A3Q007100010012070020000B4Q0034002100053Q00122Q002200153Q00122Q002300166Q00210023000200122Q002200176Q0020002200024Q001600203Q00122Q0020000B6Q002100053Q00122Q002200183Q00122Q002300196Q00210023000200122Q0022001A6Q0020002200024Q001700203Q00122Q0020000B6Q002100053Q00122Q0022001B3Q00122Q0023001C6Q00210023000200122Q0022001D6Q0020002200024Q001800203Q00122Q001200043Q0026B6001200970001001E00048A3Q009700012Q0015001F001F3Q00204A00200011000A000620001900790001002000048A3Q0079000100127A001F00013Q00048A3Q0093000100204A00200011000A000620001A007E0001002000048A3Q007E000100127A001F00043Q00048A3Q0093000100204A00200011000A000620001B00830001002000048A3Q0083000100127A001F001F3Q00048A3Q0093000100204A00200011000A000620001C00880001002000048A3Q0088000100127A001F001E3Q00048A3Q0093000100204A00200011000A000620001D008D0001002000048A3Q008D000100127A001F00203Q00048A3Q0093000100204A00200011000A000620001E00920001002000048A3Q0092000100127A001F00213Q00048A3Q0093000100204A001F0011000A0006A7001F00C800013Q00048A3Q00C800012Q0005001F00023Q00048A3Q00C800010026B6001200AF0001001F00048A3Q00AF00010006AC001C00A00001001600048A3Q00A00001001207002000223Q00204A0020002000232Q004C002100164Q00C50020000200022Q004C001C00203Q0006AC001D00A70001001700048A3Q00A70001001207002000223Q00204A0020002000232Q004C002100174Q00C50020000200022Q004C001D00203Q0006AC001E00AE0001001800048A3Q00AE0001001207002000223Q00204A0020002000232Q004C002100184Q00C50020000200022Q004C001E00203Q00127A0012001E3Q0026B60012003B0001000400048A3Q003B00010006AC001900B80001001300048A3Q00B80001001207002000223Q00204A0020002000232Q004C002100134Q00C50020000200022Q004C001900203Q0006AC001A00BF0001001400048A3Q00BF0001001207002000223Q00204A0020002000232Q004C002100144Q00C50020000200022Q004C001A00203Q0006AC001B00C60001001500048A3Q00C60001001207002000223Q00204A0020002000232Q004C002100154Q00C50020000200022Q004C001B00203Q00127A0012001F3Q00048A3Q003B0001001207001200073Q00204100120012002400202Q00120012002500202Q00120012002600202Q00120012002700202Q00120012002800062Q001200442Q013Q00048A3Q00442Q0100127A001300034Q0015001400153Q000E51000300E10001001300048A3Q00E100012Q0018001600063Q00206D0016001600294Q001700053Q00122Q0018002A3Q00122Q0019002B6Q0017001900022Q008000140016001700122Q001600223Q00202Q00160016002C4Q001700146Q0016000200024Q001500163Q00122Q001300013Q0026B6001300D20001000100048A3Q00D20001000E47000300442Q01001500048A3Q00442Q0100127A001600034Q0015001700183Q0026B6001600F90001000100048A3Q00F900010006A7001800442Q013Q00048A3Q00442Q010012070019002D3Q00204A00190019002E2Q004C001A00084Q00C5001900020002000620001800442Q01001900048A3Q00442Q012Q0018001900024Q004C001A00184Q00C500190002000200262E001900442Q01001D00048A3Q00442Q0100127A0019002F4Q0005001900023Q00048A3Q00442Q010026B6001600E70001000300048A3Q00E70001001207001900303Q00120A001A00043Q00122Q001B00223Q00202Q001B001B00314Q001C00146Q001B001C6Q00193Q00024Q001700193Q00062Q0018000A2Q01001700048A3Q000A2Q01001207001900223Q00204A0019001900232Q004C001A00174Q00C50019000200022Q004C001800193Q00127A001600013Q00048A3Q00E7000100048A3Q00442Q0100048A3Q00D2000100048A3Q00442Q01000E47000300442Q01000800048A3Q00442Q01001207001100323Q00204A0011001100332Q004C001200084Q00C50011000200020006A7001100442Q013Q00048A3Q00442Q012Q0018001100034Q00780011001000112Q0018001200043Q000677001100442Q01001200048A3Q00442Q012Q0018001100074Q0018001200084Q00C5001100020002002657001100272Q01003400048A3Q00272Q012Q0018001100074Q0018001200084Q00C50011000200022Q0018001200043Q000677001100442Q01001200048A3Q00442Q012Q0018001100094Q00180012000A4Q00C5001100020002002657001100322Q01003400048A3Q00322Q012Q0018001100094Q00180012000A4Q00C50011000200022Q0018001200043Q000677001100442Q01001200048A3Q00442Q012Q00180011000B3Q0006A7001100432Q013Q00048A3Q00432Q010006A7000F00432Q013Q00048A3Q00432Q010006A7000F00442Q013Q00048A3Q00442Q012Q00180011000C4Q006E00110001000200065F001100412Q01000100048A3Q00412Q0100065F000B00412Q01000100048A3Q00412Q010006A7000E00442Q013Q00048A3Q00442Q0100065F000D00442Q01000100048A3Q00442Q012Q0005000800023Q00127A001100034Q0005001100023Q0026B60007005D2Q01000300048A3Q005D2Q0100204A00080006000200202400110006003500202Q00090011003600202Q0011000600374Q001200053Q00122Q001300383Q00122Q001400396Q00120014000200062Q001100592Q01001200048A3Q00592Q01001207001100073Q00204800110011003A00202Q00110011003B00202Q00110011003C00202Q00110011003D00262Q0011005A2Q01003E00048A3Q005A2Q012Q002B000A6Q0003000A00014Q0003000B5Q00127A000700013Q0026B6000700110001000100048A3Q001100012Q0003000C6Q0003000D6Q0003000E6Q00180011000B3Q0006A7001100722Q013Q00048A3Q00722Q012Q00180011000D4Q00B5001200086Q001300053Q00122Q0014003F3Q00122Q001500406Q0013001500024Q001400086Q0013001300144Q0011001300144Q000E00146Q000D00136Q000C00126Q000B00113Q00127A000700043Q00048A3Q0011000100043E0002000400012Q007C3Q00017Q00033Q00028Q0003073Q0047657454696D65025Q00408F40010E3Q00127A000100013Q0026B6000100010001000100048A3Q000100010006A73Q000A00013Q00048A3Q000A0001001207000200024Q006E0002000100020020010002000200032Q007800023Q00022Q0005000200024Q0015000200024Q0005000200023Q00048A3Q000100012Q007C3Q00017Q00033Q00028Q0003073Q0047657454696D65025Q00408F40010E3Q00127A000100013Q0026B6000100010001000100048A3Q000100010006A73Q000A00013Q00048A3Q000A0001001207000200024Q006E0002000100020020010002000200032Q007800023Q00022Q0005000200024Q0015000200024Q0005000200023Q00048A3Q000100012Q007C3Q00017Q00083Q00028Q0003073Q00435F5370652Q6C03103Q004765745370652Q6C432Q6F6C646F776E0003093Q00737461727454696D6503083Q006475726174696F6E03073Q0047657454696D65025Q00408F40011B3Q00127A000100014Q0015000200023Q0026B6000100020001000100048A3Q00020001001207000300023Q0020020003000300034Q00048Q0003000200024Q000200033Q00262Q000200170001000400048A3Q0017000100204A000300020005002657000300170001000400048A3Q0017000100204A000300020006001229000400076Q00040001000200202Q0005000200054Q0004000400054Q00030003000400202Q00030003000800062Q000300180001000100048A3Q0018000100127A000300014Q0005000300023Q00048A3Q000200012Q007C3Q00017Q00053Q00028Q0003063Q00435F4974656D030F3Q004765744974656D432Q6F6C646F776E03073Q0047657454696D65025Q00408F4001183Q00127A000100014Q0015000200043Q000E51000100020001000100048A3Q00020001001207000500023Q0020110005000500034Q00068Q0005000200074Q000400076Q000300066Q000200053Q00262Q000200140001000100048A3Q00140001001207000500044Q00900005000100024Q0005000500024Q00050003000500202Q00050005000500062Q000500150001000100048A3Q0015000100127A000500014Q0005000500023Q00048A3Q000200012Q007C3Q00017Q00093Q00028Q0003063Q0048724461746103073Q005370652Q6C494400030C3Q004379636C655370652Q6C494403073Q004379636C654D4F03073Q00C311201D834A0103083Q001693634970E2387803073Q005072696D61727900373Q0012C03Q00016Q00015Q00202Q00010001000200202Q00010001000300262Q0001000E0001000400048A3Q000E00012Q001800015Q00204A00010001000200204A000100010003000E470001000E0001000100048A3Q000E00012Q001800015Q00204A00010001000200204A3Q000100032Q001800015Q00204A00010001000200204A000100010005002657000100200001000400048A3Q002000012Q001800015Q00204A00010001000200204A000100010006002657000100200001000400048A3Q002000012Q001800015Q00204A00010001000200204A000100010005000E47000100200001000100048A3Q002000012Q001800015Q00204A00010001000200204A3Q000100052Q001000013Q00012Q009A000200013Q00122Q000300073Q00122Q000400086Q00020004000200202Q0001000200010006AD00023Q0001000A2Q00183Q00024Q00183Q00034Q00183Q00044Q00183Q00054Q00183Q00014Q00188Q00183Q00064Q00183Q00074Q00183Q00084Q00183Q00094Q0026000300026Q00048Q00030002000200102Q0001000900034Q000100028Q00013Q00013Q002B3Q00028Q00026Q003940025Q00C05240027Q004003063Q00435F4974656D03123Q004765744974656D496E666F496E7374616E74026Q000840026Q00F03F03143Q00476574496E76656E746F72794974656D4C696E6B03063Q00A879E3EC88AA03053Q00EDD8158295026Q002E4003063Q0092425E46B5DB03073Q003EE22E2Q3FD0A9026Q002440026Q001040026Q001840026Q001C4003083Q0053652Q74696E6773030D3Q00C12966B310192651EB37548E1A03083Q003E857935E37F6D4F030C3Q004765744974656D436F756E7403043Q006D6174682Q033Q00616273026Q00144003063Q0073656C656374030B3Q004765744974656D496E666F03064Q001833ECD3BC03073Q00C270745295B6CE026Q002A4003063Q0029A44D01C5F003073Q006E59C82C78A082026Q002C4003063Q00BBCF4A5F465803083Q002DCBA32B26232A5B026Q00304003063Q00C289DD3A82BB03073Q0034B2E5BC43E7C9026Q00314003073Q00435F5370652Q6C030D3Q0049735370652Q6C557361626C65026Q0059400001F83Q0006A73Q00F700013Q00048A3Q00F700012Q004C00016Q001800026Q004C000300014Q00C5000200020002000E47000100CE0001000100048A3Q00CE00012Q0018000300014Q003C000400016Q0003000200024Q000400026Q0003000300044Q000400033Q00202Q00040004000200202Q00040004000300062Q000300CE0001000400048A3Q00CE000100127A000300014Q0015000400123Q0026B6000300330001000400048A3Q003300010006AC000C001D0001000600048A3Q001D0001001207001300053Q00204A0013001300062Q004C001400064Q00C50013000200022Q004C000C00133Q0006AC000D00240001000700048A3Q00240001001207001300053Q00204A0013001300062Q004C001400074Q00C50013000200022Q004C000D00133Q0006AC000E002B0001000800048A3Q002B0001001207001300053Q00204A0013001300062Q004C001400084Q00C50013000200022Q004C000E00133Q0006AC000F00320001000900048A3Q00320001001207001300053Q00204A0013001300062Q004C001400094Q00C50013000200022Q004C000F00133Q00127A000300073Q0026B6000300540001000800048A3Q00540001001207001300094Q00B0001400043Q00122Q0015000A3Q00122Q0016000B6Q00140016000200122Q0015000C6Q0013001500024Q000800133Q00122Q001300096Q001400043Q00122Q0015000D3Q00122Q0016000E6Q00140016000200122Q0015000F6Q0013001500024Q000900133Q00062Q000A004C0001000400048A3Q004C0001001207001300053Q00204A0013001300062Q004C001400044Q00C50013000200022Q004C000A00133Q0006AC000B00530001000500048A3Q00530001001207001300053Q00204A0013001300062Q004C001400054Q00C50013000200022Q004C000B00133Q00127A000300043Q000E51000700790001000300048A3Q007900012Q0015001000103Q000620000A005B0001000100048A3Q005B000100127A001000083Q00048A3Q006E0001000620000B005F0001000100048A3Q005F000100127A001000043Q00048A3Q006E0001000620000C00630001000100048A3Q0063000100127A001000073Q00048A3Q006E0001000620000D00670001000100048A3Q0067000100127A001000103Q00048A3Q006E0001000620000E006B0001000100048A3Q006B000100127A001000113Q00048A3Q006E0001000620000F006E0001000100048A3Q006E000100127A001000123Q0006A70010007100013Q00048A3Q007100012Q0005001000024Q0018001300053Q00206D0013001300134Q001400043Q00122Q001500143Q00122Q001600156Q0014001600022Q005800110013001400127A000300103Q000E51001000AA0001000300048A3Q00AA0001001207001300053Q00207E0013001300164Q001400116Q0013000200024Q001200133Q000E2Q000100CE0001001200048A3Q00CE000100127A001300014Q0015001400153Q0026B6001300960001000800048A3Q009600010006A7001500CE00013Q00048A3Q00CE0001001207001600173Q00204A0016001600182Q004C001700014Q00C5001600020002000620001500CE0001001600048A3Q00CE00012Q0018001600014Q004C001700154Q00C500160002000200262E001600CE0001000F00048A3Q00CE000100127A001600194Q0005001600023Q00048A3Q00CE00010026B6001300840001000100048A3Q008400010012070016001A3Q00120A001700043Q00122Q001800053Q00202Q00180018001B4Q001900116Q001800196Q00163Q00024Q001400163Q00062Q001500A70001001400048A3Q00A70001001207001600053Q00204A0016001600062Q004C001700144Q00C50016000200022Q004C001500163Q00127A001300083Q00048A3Q0084000100048A3Q00CE00010026B6000300140001000100048A3Q00140001001207001300094Q00C2001400043Q00122Q0015001C3Q00122Q0016001D6Q00140016000200122Q0015001E6Q0013001500024Q000400133Q00122Q001300096Q001400043Q00122Q0015001F3Q00122Q001600206Q00140016000200122Q001500216Q0013001500024Q000500133Q00122Q001300096Q001400043Q00122Q001500223Q00122Q001600236Q00140016000200122Q001500246Q0013001500024Q000600133Q00122Q001300096Q001400043Q00122Q001500253Q00122Q001600266Q00140016000200122Q001500276Q0013001500024Q000700133Q00122Q000300083Q00044Q00140001000E47000100F50001000100048A3Q00F50001001207000300283Q00204A0003000300292Q004C000400014Q00C50003000200020006A7000300F500013Q00048A3Q00F500012Q0018000300024Q00780003000200032Q0018000400033Q00205B00040004002A000677000300F50001000400048A3Q00F500012Q0018000300064Q0018000400074Q00C5000300020002002657000300E80001002B00048A3Q00E800012Q0018000300064Q0006000400076Q0003000200024Q000400033Q00202Q00040004002A00062Q000300F50001000400048A3Q00F500012Q0018000300084Q0018000400094Q00C5000300020002002657000300F40001002B00048A3Q00F400012Q0018000300084Q0006000400096Q0003000200024Q000400033Q00202Q00040004002A00062Q000300F50001000400048A3Q00F500012Q0005000100023Q00127A000300014Q0005000300024Q007C3Q00017Q00",
    GetFEnv(), ...);