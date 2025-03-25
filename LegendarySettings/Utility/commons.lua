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
                if (Enum <= 142) then
                    if (Enum <= 70) then
                        if (Enum <= 34) then
                            if (Enum <= 16) then
                                if (Enum <= 7) then
                                    if (Enum <= 3) then
                                        if (Enum <= 1) then
                                            if (Enum == 0) then
                                                Stk[Inst[2]] = Env[Inst[3]];
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
                                                if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                                    VIP = VIP + 1;
                                                else
                                                    VIP = Inst[3];
                                                end
                                            end
                                        elseif (Enum == 2) then
                                            local A;
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
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        else
                                            local A;
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
                                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            VIP = Inst[3];
                                        end
                                    elseif (Enum <= 5) then
                                        if (Enum > 4) then
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
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            VIP = Inst[3];
                                        else
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
                                        end
                                    elseif (Enum > 6) then
                                        Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
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
                                elseif (Enum <= 11) then
                                    if (Enum <= 9) then
                                        if (Enum > 8) then
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
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                        end
                                    elseif (Enum == 10) then
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
                                        local Edx;
                                        local Results;
                                        local A;
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
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
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
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        VIP = Inst[3];
                                    end
                                elseif (Enum <= 13) then
                                    if (Enum > 12) then
                                        local A = Inst[2];
                                        local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                        local Edx = 0;
                                        for Idx = A, Inst[4] do
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
                                        Stk[Inst[2]] = Inst[3];
                                    end
                                elseif (Enum <= 14) then
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
                                elseif (Enum == 15) then
                                    local A = Inst[2];
                                    do
                                        return Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    end
                                else
                                    local A;
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
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
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                end
                            elseif (Enum <= 25) then
                                if (Enum <= 20) then
                                    if (Enum <= 18) then
                                        if (Enum > 17) then
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
                                        else
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
                                        end
                                    elseif (Enum == 19) then
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
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
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
                                        for Idx = Inst[2], Inst[3] do
                                            Stk[Idx] = nil;
                                        end
                                    end
                                elseif (Enum <= 22) then
                                    if (Enum > 21) then
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
                                    else
                                        local Results;
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    end
                                elseif (Enum <= 23) then
                                    local A;
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
                                    do
                                        return Stk[Inst[2]];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                elseif (Enum == 24) then
                                    local B = Stk[Inst[4]];
                                    if B then
                                        VIP = VIP + 1;
                                    else
                                        Stk[Inst[2]] = B;
                                        VIP = Inst[3];
                                    end
                                else
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
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 29) then
                                if (Enum <= 27) then
                                    if (Enum > 26) then
                                        local A;
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
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
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
                                    else
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
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        for Idx = Inst[2], Inst[3] do
                                            Stk[Idx] = nil;
                                        end
                                    end
                                elseif (Enum > 28) then
                                    if (Stk[Inst[2]] ~= Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 31) then
                                if (Enum > 30) then
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
                                else
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
                                end
                            elseif (Enum <= 32) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
                            elseif (Enum == 33) then
                                local Edx;
                                local Results;
                                local A;
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
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = #Stk[Inst[3]];
                            end
                        elseif (Enum <= 52) then
                            if (Enum <= 43) then
                                if (Enum <= 38) then
                                    if (Enum <= 36) then
                                        if (Enum > 35) then
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
                                            Stk[Inst[2]] = Env[Inst[3]];
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
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            VIP = Inst[3];
                                        else
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
                                        end
                                    elseif (Enum > 37) then
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]];
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
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
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
                                    if (Enum == 39) then
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = Inst[3];
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
                                    else
                                        local A;
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = not Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    end
                                elseif (Enum <= 41) then
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
                                elseif (Enum == 42) then
                                    local Edx;
                                    local Results, Limit;
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
                                end
                            elseif (Enum <= 47) then
                                if (Enum <= 45) then
                                    if (Enum > 44) then
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
                                elseif (Enum == 46) then
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
                                else
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
                                end
                            elseif (Enum <= 49) then
                                if (Enum > 48) then
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
                                else
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
                                end
                            elseif (Enum <= 50) then
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
                            elseif (Enum > 51) then
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
                            end
                        elseif (Enum <= 61) then
                            if (Enum <= 56) then
                                if (Enum <= 54) then
                                    if (Enum > 53) then
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
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
                                    else
                                        local A;
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
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 55) then
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                            elseif (Enum <= 58) then
                                if (Enum == 57) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
                                elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = VIP + Inst[3];
                                end
                            elseif (Enum <= 59) then
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
                            elseif (Enum > 60) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
                                local A = Inst[2];
                                local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
                                Top = (Limit + A) - 1;
                                local Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                            end
                        elseif (Enum <= 65) then
                            if (Enum <= 63) then
                                if (Enum == 62) then
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                else
                                    do
                                        return;
                                    end
                                end
                            elseif (Enum > 64) then
                                if (Stk[Inst[2]] < Stk[Inst[4]]) then
                                    VIP = Inst[3];
                                else
                                    VIP = VIP + 1;
                                end
                            else
                                local K;
                                local B;
                                local A;
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
                            end
                        elseif (Enum <= 67) then
                            if (Enum > 66) then
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
                            else
                                local A;
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
                            end
                        elseif (Enum <= 68) then
                            local Edx;
                            local Results, Limit;
                            local B;
                            local A;
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                            Stk[Inst[2]] = Env[Inst[3]];
                        elseif (Enum == 69) then
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
                        else
                            local A;
                            Stk[Inst[2]] = Env[Inst[3]];
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
                        end
                    elseif (Enum <= 106) then
                        if (Enum <= 88) then
                            if (Enum <= 79) then
                                if (Enum <= 74) then
                                    if (Enum <= 72) then
                                        if (Enum == 71) then
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
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
                                        end
                                    elseif (Enum > 73) then
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if not Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
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
                                        if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum <= 76) then
                                    if (Enum == 75) then
                                        local B;
                                        local A;
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    else
                                        local Results;
                                        local Edx;
                                        local Results, Limit;
                                        local B;
                                        local A;
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
                                        Stk[Inst[2]] = Env[Inst[3]];
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
                                        Stk[Inst[2]] = Inst[3];
                                    end
                                elseif (Enum <= 77) then
                                    local Edx;
                                    local Results, Limit;
                                    local B;
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                elseif (Enum > 78) then
                                    local Edx;
                                    local Results;
                                    local A;
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
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
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
                                    Stk[Inst[2]] = Inst[3];
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                end
                            elseif (Enum <= 83) then
                                if (Enum <= 81) then
                                    if (Enum == 80) then
                                        local A;
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
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Upvalues[Inst[3]] = Stk[Inst[2]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Upvalues[Inst[3]] = Stk[Inst[2]];
                                    else
                                        Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
                                    end
                                elseif (Enum > 82) then
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
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
                                    do
                                        return;
                                    end
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
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 85) then
                                if (Enum == 84) then
                                    local Edx;
                                    local Results, Limit;
                                    local B;
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    local A;
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
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] > Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = VIP + Inst[3];
                                    end
                                end
                            elseif (Enum <= 86) then
                                Env[Inst[3]] = Stk[Inst[2]];
                            elseif (Enum > 87) then
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
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] <= Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
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
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 97) then
                            if (Enum <= 92) then
                                if (Enum <= 90) then
                                    if (Enum == 89) then
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
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
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
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        VIP = Inst[3];
                                    else
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
                                    end
                                elseif (Enum > 91) then
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                else
                                    local A;
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
                                end
                            elseif (Enum <= 94) then
                                if (Enum > 93) then
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
                                end
                            elseif (Enum <= 95) then
                                local Edx;
                                local Results, Limit;
                                local A;
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
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 96) then
                                local A = Inst[2];
                                local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
                                local Edx = 0;
                                for Idx = A, Inst[4] do
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
                        elseif (Enum <= 101) then
                            if (Enum <= 99) then
                                if (Enum > 98) then
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
                                else
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
                                    Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
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
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                end
                            elseif (Enum == 100) then
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
                            else
                                local A;
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
                            end
                        elseif (Enum <= 103) then
                            if (Enum == 102) then
                                Stk[Inst[2]]();
                            else
                                local A = Inst[2];
                                Stk[A] = Stk[A]();
                            end
                        elseif (Enum <= 104) then
                            if (Stk[Inst[2]] > Inst[4]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum == 105) then
                            if (Stk[Inst[2]] < Stk[Inst[4]]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 124) then
                        if (Enum <= 115) then
                            if (Enum <= 110) then
                                if (Enum <= 108) then
                                    if (Enum == 107) then
                                        local K;
                                        local B;
                                        local A;
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
                                        B = Stk[Inst[4]];
                                        if not B then
                                            VIP = VIP + 1;
                                        else
                                            Stk[Inst[2]] = B;
                                            VIP = Inst[3];
                                        end
                                    else
                                        local A;
                                        local K;
                                        local B;
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
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
                                        Stk[A] = Stk[A](Stk[A + 1]);
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
                                        if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum == 109) then
                                    if Stk[Inst[2]] then
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
                                    VIP = Inst[3];
                                end
                            elseif (Enum <= 112) then
                                if (Enum > 111) then
                                    local A;
                                    A = Inst[2];
                                    Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
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
                                    if (Stk[Inst[2]] == Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 113) then
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
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 114) then
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
                                local A;
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 119) then
                            if (Enum <= 117) then
                                if (Enum == 116) then
                                    local A = Inst[2];
                                    local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    local Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                else
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
                                end
                            elseif (Enum > 118) then
                                local A = Inst[2];
                                Stk[A](Stk[A + 1]);
                            else
                                local Edx;
                                local Results;
                                local A;
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
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
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            end
                        elseif (Enum <= 121) then
                            if (Enum > 120) then
                                local A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] > Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 122) then
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
                        elseif (Enum > 123) then
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
                        else
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 133) then
                        if (Enum <= 128) then
                            if (Enum <= 126) then
                                if (Enum == 125) then
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
                                else
                                    do
                                        return Stk[Inst[2]];
                                    end
                                end
                            elseif (Enum == 127) then
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
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
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 130) then
                            if (Enum > 129) then
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
                            else
                                local A;
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
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Upvalues[Inst[3]] = Stk[Inst[2]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Upvalues[Inst[3]] = Stk[Inst[2]];
                            end
                        elseif (Enum <= 131) then
                            Stk[Inst[2]] = {};
                        elseif (Enum > 132) then
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
                            local Edx;
                            local Results, Limit;
                            local B;
                            local A;
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                        end
                    elseif (Enum <= 137) then
                        if (Enum <= 135) then
                            if (Enum > 134) then
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
                            else
                                Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
                            end
                        elseif (Enum == 136) then
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                        end
                    elseif (Enum <= 139) then
                        if (Enum == 138) then
                            local Edx;
                            local Results, Limit;
                            local B;
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
                            Stk[Inst[2]] = Env[Inst[3]];
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
                            A = Inst[2];
                            B = Stk[Inst[3]];
                            Stk[A + 1] = B;
                            Stk[A] = B[Inst[4]];
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
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
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
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            B = Stk[Inst[3]];
                            Stk[A + 1] = B;
                            Stk[A] = B[Inst[4]];
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
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        else
                            local B;
                            local Edx;
                            local Results, Limit;
                            local A;
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
                            B = Stk[Inst[4]];
                            if not B then
                                VIP = VIP + 1;
                            else
                                Stk[Inst[2]] = B;
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 140) then
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
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    elseif (Enum == 141) then
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
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        B = Stk[Inst[4]];
                        if B then
                            VIP = VIP + 1;
                        else
                            Stk[Inst[2]] = B;
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum <= 213) then
                    if (Enum <= 177) then
                        if (Enum <= 159) then
                            if (Enum <= 150) then
                                if (Enum <= 146) then
                                    if (Enum <= 144) then
                                        if (Enum > 143) then
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
                                            if Stk[Inst[2]] then
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
                                        end
                                    elseif (Enum > 145) then
                                        local A;
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
                                        Upvalues[Inst[3]] = Stk[Inst[2]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        VIP = Inst[3];
                                    else
                                        local A;
                                        A = Inst[2];
                                        Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    end
                                elseif (Enum <= 148) then
                                    if (Enum > 147) then
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
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
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
                                        if not Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
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
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] > Inst[4]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum > 149) then
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
                                else
                                    local A = Inst[2];
                                    local Results, Limit = _R(Stk[A](Stk[A + 1]));
                                    Top = (Limit + A) - 1;
                                    local Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                end
                            elseif (Enum <= 154) then
                                if (Enum <= 152) then
                                    if (Enum == 151) then
                                        local A;
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
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
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
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
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
                                    else
                                        local Edx;
                                        local Results, Limit;
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
                                    end
                                elseif (Enum > 153) then
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                end
                            elseif (Enum <= 156) then
                                if (Enum == 155) then
                                    local A = Inst[2];
                                    local Results = {Stk[A]()};
                                    local Limit = Inst[4];
                                    local Edx = 0;
                                    for Idx = A, Limit do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                else
                                    local B;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
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
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 157) then
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            elseif (Enum > 158) then
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
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
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
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 168) then
                            if (Enum <= 163) then
                                if (Enum <= 161) then
                                    if (Enum > 160) then
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
                                        if (Stk[Inst[2]] ~= Inst[4]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum == 162) then
                                    local A = Inst[2];
                                    do
                                        return Unpack(Stk, A, A + Inst[3]);
                                    end
                                else
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
                                end
                            elseif (Enum <= 165) then
                                if (Enum == 164) then
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
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
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    local A = Inst[2];
                                    do
                                        return Unpack(Stk, A, Top);
                                    end
                                end
                            elseif (Enum <= 166) then
                                local A = Inst[2];
                                local T = Stk[A];
                                for Idx = A + 1, Top do
                                    Insert(T, Stk[Idx]);
                                end
                            elseif (Enum == 167) then
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            else
                                local A;
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
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 172) then
                            if (Enum <= 170) then
                                if (Enum > 169) then
                                    local A;
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
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
                                else
                                    local Edx;
                                    local Results, Limit;
                                    local B;
                                    local A;
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
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                end
                            elseif (Enum > 171) then
                                local A;
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                for Idx = Inst[2], Inst[3] do
                                    Stk[Idx] = nil;
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] < Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
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
                            end
                        elseif (Enum <= 174) then
                            if (Enum > 173) then
                                local B;
                                local Edx;
                                local Results, Limit;
                                local A;
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
                                B = Stk[Inst[4]];
                                if not B then
                                    VIP = VIP + 1;
                                else
                                    Stk[Inst[2]] = B;
                                    VIP = Inst[3];
                                end
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
                        elseif (Enum <= 175) then
                            local Edx;
                            local Results, Limit;
                            local A;
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
                        elseif (Enum > 176) then
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
                        else
                            local A = Inst[2];
                            Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        end
                    elseif (Enum <= 195) then
                        if (Enum <= 186) then
                            if (Enum <= 181) then
                                if (Enum <= 179) then
                                    if (Enum > 178) then
                                        local A = Inst[2];
                                        local B = Inst[3];
                                        for Idx = A, B do
                                            Stk[Idx] = Vararg[Idx - A];
                                        end
                                    else
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
                                        if not Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum > 180) then
                                    if (Stk[Inst[2]] == Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
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
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 183) then
                                if (Enum > 182) then
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
                                elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum <= 184) then
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                            elseif (Enum == 185) then
                                Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
                            else
                                local A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            end
                        elseif (Enum <= 190) then
                            if (Enum <= 188) then
                                if (Enum > 187) then
                                    Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                else
                                    local A;
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
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
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
                                    Stk[Inst[2]] = #Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                end
                            elseif (Enum > 189) then
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
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
                                local A;
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
                                Stk[Inst[2]] = Inst[3] ~= 0;
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
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] ~= 0;
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
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] ~= 0;
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
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] ~= 0;
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
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] ~= 0;
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
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] ~= 0;
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
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] ~= 0;
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
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] ~= 0;
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
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] ~= 0;
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            end
                        elseif (Enum <= 192) then
                            if (Enum == 191) then
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
                            end
                        elseif (Enum <= 193) then
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
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 194) then
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                        else
                            local Edx;
                            local Results, Limit;
                            local A;
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
                            Stk[Inst[2]] = Inst[3];
                        end
                    elseif (Enum <= 204) then
                        if (Enum <= 199) then
                            if (Enum <= 197) then
                                if (Enum == 196) then
                                    local A;
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
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    local A;
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
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Upvalues[Inst[3]] = Stk[Inst[2]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Upvalues[Inst[3]] = Stk[Inst[2]];
                                end
                            elseif (Enum > 198) then
                                local A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                            else
                                local A;
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                                Stk[Inst[2]] = Inst[3];
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
                                Stk[Inst[2]] = Inst[3];
                            end
                        elseif (Enum <= 201) then
                            if (Enum > 200) then
                                Upvalues[Inst[3]] = Stk[Inst[2]];
                            else
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A]();
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
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 202) then
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
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
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum == 203) then
                            local Step;
                            local Index;
                            local A;
                            Stk[Inst[2]] = {};
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
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
                            Stk[Inst[2]] = not Stk[Inst[3]];
                        end
                    elseif (Enum <= 208) then
                        if (Enum <= 206) then
                            if (Enum > 205) then
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
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
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
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
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
                        elseif (Enum == 207) then
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
                        end
                    elseif (Enum <= 210) then
                        if (Enum > 209) then
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                        else
                            local Edx;
                            local Results, Limit;
                            local A;
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
                            Stk[Inst[2]] = Stk[Inst[3]];
                        end
                    elseif (Enum <= 211) then
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
                    elseif (Enum == 212) then
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
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    else
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
                    end
                elseif (Enum <= 249) then
                    if (Enum <= 231) then
                        if (Enum <= 222) then
                            if (Enum <= 217) then
                                if (Enum <= 215) then
                                    if (Enum > 214) then
                                        if not Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        local Edx;
                                        local Results;
                                        local A;
                                        Stk[Inst[2]] = Env[Inst[3]];
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
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    end
                                elseif (Enum > 216) then
                                    local A = Inst[2];
                                    local B = Stk[Inst[3]];
                                    Stk[A + 1] = B;
                                    Stk[A] = B[Inst[4]];
                                else
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
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
                                    A = Inst[2];
                                    Stk[A] = Stk[A]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 219) then
                                if (Enum == 218) then
                                    local B = Inst[3];
                                    local K = Stk[B];
                                    for Idx = B + 1, Inst[4] do
                                        K = K .. Stk[Idx];
                                    end
                                    Stk[Inst[2]] = K;
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
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
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
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
                            elseif (Enum <= 220) then
                                local Edx;
                                local Results, Limit;
                                local B;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            elseif (Enum > 221) then
                                local B = Stk[Inst[4]];
                                if not B then
                                    VIP = VIP + 1;
                                else
                                    Stk[Inst[2]] = B;
                                    VIP = Inst[3];
                                end
                            else
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
                            end
                        elseif (Enum <= 226) then
                            if (Enum <= 224) then
                                if (Enum > 223) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
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
                                    local Edx;
                                    local Results, Limit;
                                    local A;
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
                                end
                            elseif (Enum > 225) then
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
                            else
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 228) then
                            if (Enum == 227) then
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
                                    if (Mvm[1] == 253) then
                                        Indexes[Idx - 1] = {Stk, Mvm[3]};
                                    else
                                        Indexes[Idx - 1] = {Upvalues, Mvm[3]};
                                    end
                                    Lupvals[#Lupvals + 1] = Indexes;
                                end
                                Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
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
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 229) then
                            local A;
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
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        elseif (Enum > 230) then
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
                        else
                            local A;
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                    elseif (Enum <= 240) then
                        if (Enum <= 235) then
                            if (Enum <= 233) then
                                if (Enum > 232) then
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
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
                                    for Idx = Inst[2], Inst[3] do
                                        Stk[Idx] = nil;
                                    end
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
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
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
                                end
                            elseif (Enum > 234) then
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
                                Stk[Inst[2]] = Env[Inst[3]];
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
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            else
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
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
                            end
                        elseif (Enum <= 237) then
                            if (Enum > 236) then
                                local A;
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] <= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
                            end
                        elseif (Enum <= 238) then
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
                        elseif (Enum == 239) then
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
                            local A = Inst[2];
                            Stk[A] = Stk[A](Stk[A + 1]);
                        end
                    elseif (Enum <= 244) then
                        if (Enum <= 242) then
                            if (Enum == 241) then
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
                            else
                                local A;
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
                                Stk[Inst[2]] = Stk[Inst[3]];
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
                        elseif (Enum == 243) then
                            if (Inst[2] == Stk[Inst[4]]) then
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
                    elseif (Enum <= 246) then
                        if (Enum > 245) then
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
                        else
                            Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
                        end
                    elseif (Enum <= 247) then
                        local A;
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
                        Stk[Inst[2]][Inst[3]] = Inst[4];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Inst[3]] = Inst[4];
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
                        Stk[Inst[2]][Inst[3]] = Inst[4];
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
                        Stk[Inst[2]][Inst[3]] = Inst[4];
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
                        Stk[Inst[2]][Inst[3]] = Inst[4];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Inst[3]] = Inst[4];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Inst[3]] = Inst[4];
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
                    elseif (Enum > 248) then
                        if (Stk[Inst[2]] <= Inst[4]) then
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
                        Stk[Inst[2]] = Inst[3] ~= 0;
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
                elseif (Enum <= 267) then
                    if (Enum <= 258) then
                        if (Enum <= 253) then
                            if (Enum <= 251) then
                                if (Enum == 250) then
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
                                end
                            elseif (Enum == 252) then
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = Stk[Inst[3]];
                            end
                        elseif (Enum <= 255) then
                            if (Enum == 254) then
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 256) then
                            Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                        elseif (Enum == 257) then
                            for Idx = Inst[2], Inst[3] do
                                Stk[Idx] = nil;
                            end
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
                            if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 262) then
                        if (Enum <= 260) then
                            if (Enum > 259) then
                                local A;
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
                                VIP = Inst[3];
                            else
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
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum == 261) then
                            Stk[Inst[2]] = Inst[3] ~= 0;
                        else
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
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
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
                        end
                    elseif (Enum <= 264) then
                        if (Enum == 263) then
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
                            Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
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
                    elseif (Enum <= 265) then
                        Stk[Inst[2]] = Inst[3];
                    elseif (Enum == 266) then
                        local A;
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
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                    end
                elseif (Enum <= 276) then
                    if (Enum <= 271) then
                        if (Enum <= 269) then
                            if (Enum > 268) then
                                Env[Inst[3]] = Stk[Inst[2]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Inst[2] < Stk[Inst[4]]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum == 270) then
                            if (Stk[Inst[2]] < Inst[4]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                        end
                    elseif (Enum <= 273) then
                        if (Enum == 272) then
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
                    elseif (Enum <= 274) then
                        local A;
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
                        Stk[Inst[2]] = Inst[3];
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
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                        Stk[Inst[2]] = Inst[3];
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
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                        Stk[Inst[2]] = Inst[3];
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
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                        Stk[Inst[2]] = Inst[3];
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
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                        Stk[Inst[2]] = Inst[3];
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
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                        Stk[Inst[2]] = Inst[3];
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
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                    elseif (Enum > 275) then
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
                        Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
                    end
                elseif (Enum <= 280) then
                    if (Enum <= 278) then
                        if (Enum > 277) then
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
                    elseif (Enum == 279) then
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
                        if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum <= 282) then
                    if (Enum == 281) then
                        local B;
                        local Edx;
                        local Results, Limit;
                        local A;
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
                    else
                        local A;
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
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Upvalues[Inst[3]] = Stk[Inst[2]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Upvalues[Inst[3]] = Stk[Inst[2]];
                    end
                elseif (Enum <= 283) then
                    Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
                elseif (Enum > 284) then
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
                    if (Stk[Inst[2]] <= Stk[Inst[4]]) then
                        VIP = VIP + 1;
                    else
                        VIP = Inst[3];
                    end
                else
                    local A;
                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
                end
                VIP = VIP + 1;
            end
        end;
    end
    return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall(
    "LOL!F0012Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403113Q004C6567656E6461727953652Q74696E6773030B3Q00426967576967734461746103083Q00F22C93455AD82C9303053Q003BBF49E036028Q0003063Q00D40DEFC7E31103043Q00A987629A03063Q0048724461746103083Q00E8763740C936D0DF03073Q00A8AB1744349D53034Q00030C3Q00D768F6A1201E97F17DF9840103073Q00E7941195CD454D03073Q00A3BEC4F752D2AF03063Q009FE0C7A79B37010003093Q00D4EA3FDEF2C632DBE303043Q00B297935C03053Q00B8F247371C03073Q001AEC9D2C52722C00030A3Q000421C172241CD4552D2B03043Q003B4A4EB503073Q0016C15F56BF0CF503053Q00D345B12Q3A030D3Q0083E46BF2ECDF9EEB54F0E5CEB203063Q00ABD785199589030D3Q00D5C920FDEA24D54CD3C93CFDEA03083Q002281A8529A8F509C030E3Q00B1B3210C4D5AA08B812307495D8103073Q00E9E5D2536B282E030A3Q00476C6F62616C4461746103073Q00F25237DA09E86603053Q0065A12252B603053Q00CB145AF2DE03083Q004E886D399EBB82E2030E3Q001D30F6FD3A30EEFF0A30FEF6323A03043Q00915E5F99030C3Q00DBC413DD5A85F8C015DC40A403063Q00D79DAD74B52E030E3Q0010BA8EFFD330A7A2FCF730B88EF703053Q00BA55D4EB92030E3Q00E78F13F330EB4BEB8F24FF37E95D03073Q0038A2E1769E598E030D3Q006E04CEA827EC5331C1BD25DD4803063Q00B83C65A0CF42030E3Q00038D68BD258B73B2198770AC349003043Q00DC51E21C030B3Q004372656174654672616D6503053Q0035C783F6EF03063Q00A773B5E29B8A030D3Q0052656769737465724576656E7403143Q00D20EC6655E43F9D007C079554EE3CC03C5705E5503073Q00A68242873C1B1103153Q007466EF4C157675FC50176164F15119776BEC59156003053Q0050242AAE1503093Q0053657453637269707403073Q00611E126C4B1E2303043Q001A2E705703023Q005F47030D3Q004C44697370656C43616368654C03083Q0053652Q74696E6773030B3Q0083FD1736A78BD50232A79503053Q00C2E794644603123Q004765744E756D47726F75704D656D62657273026Q00F03F026Q003940024Q00509413412Q01024Q0058941341024Q0048C21341024Q00C8CE1541024Q0024411841024Q00806A1441024Q005C091541024Q004068DD40024Q004C0D1441024Q00580F1441024Q0098690B41024Q00302F1441024Q00289A1541024Q00346E1541024Q0034651541024Q0050DA0241024Q004C321541024Q00B4641641024Q00804A1641024Q00B84B1641024Q00E0AA1341024Q0028B10D41024Q00D8590D41024Q0060C20B41024Q0038F90B41024Q0040D91641024Q00980A1741024Q003CD01841024Q00ECC01741024Q00E0F71041024Q0014EA1941024Q00B4AA1841025Q00C31841024Q0098BF1841024Q0064601941024Q00085D1941024Q008C381941024Q000C3A1941024Q0004F31941024Q003C801941024Q0054C61A41024Q00343E1B41024Q00BC2A1C41024Q00D02A1C41024Q00F42A1C41025Q002B1C41024Q000C2B1C41024Q00F8311C41024Q00D4361A41024Q0068E91C41024Q00C4E91C4103043Q006863EF8603063Q00A8262CA1C396030B3Q00A2F3977A34EDA41089EF9603083Q0076E09CE2165088D603103Q0063E0508D43FA5C8402CA4C854EE74A9403043Q00E0228E39031B3Q0044756E67656F6E2Q6572277320547261696E696E672044752Q6D7903173Q00526169646572277320547261696E696E672044752Q6D79030E3Q00EAB5C4D47DF853099E832QD07EE803083Q006EBEC7A5BD13913D031E3Q00426C61636B20447261676F6E2773204368612Q6C656E67652044752Q6D7903153Q00F9E772E99DC29ADF65E982C9D3E570A8AFD2D7E66E03063Q00A7BA8B1788EB03113Q0034BA9A001BB9C8391BBB834D3EA085002Q03043Q006D7AD5E803123Q00DEE19270DAE5A339E0FEAC37AED3B73DE3EE03043Q00508E97C203183Q0036C8734911C57E581A86475E02C5634500C3376816CB7A5503043Q002C63A61703163Q0052616964657227732054616E6B696E672044752Q6D79031A3Q0044756E67656F6E2Q657227732054616E6B696E672044752Q6D7903143Q004FE028243EE448E5283F3DAD72F0691226A971EE03063Q00C41C9749565303143Q00DD0C3B1D8354585EF60225198C5F5852E60E240903083Q001693634970E2387803123Q009C60ECF288B77BA2C18CB67EA2D198B578FB03053Q00EDD815829503153Q00A9472Q53B1CB52870E7B5EBDC859870E7B4ABDC44703073Q003EE22E2Q3FD0A9030C3Q00D11847841A196F7AF014589A03083Q003E857935E37F6D4F03193Q00496E697469617465277320547261696E696E672044752Q6D7903143Q0034013CF2D3A1AC503033F8D7A9A7503027F8DBB703073Q00C270745295B6CE03163Q00426F786572277320547261696E696E672044752Q6D7903173Q0009BA4908C6ED012DE8780AC1EB0030A64B58E4F70334B103073Q006E59C82C78A08203183Q005665746572616E277320547261696E696E672044752Q6D7903193Q004469736369706C65277320547261696E696E672044752Q6D79031C3Q0045626F6E204B6E69676874277320547261696E696E672044752Q6D7903163Q009FCB4E544247345FAE8368494E483A59EBE75E4B4E5303083Q002DCBA32B26232A5B03213Q00FF8ACE3786BB14E680DD2EC78850C484D22082AD14E684CE2482BD14F690D12E9E03073Q0034B2E5BC43E7C903123Q00064F5F08FB1C1720535701E31C07344C5D1D03073Q004341213064973C031A3Q00EAE5FDCABEF6EABECAFCC9E2AA98C7DEF5A9DDE79FC3BBD5FEC603053Q0093BF87CEB8030C3Q00A727ABC3D947F2A03DABCCC103073Q00D2E448C6A1B83303153Q00174DE5117DCD334DB32472DC314CE75057DB3B44EA03063Q00AE562993701303103Q007A0E8C1F2A0218A85A0CCD2F30021CB203083Q00CB3B60ED6B456F7103194Q0019B9E671C4D23702ECAC71D8D2251AA5EF36B0F3311BA1F803073Q00B74476CC81519003153Q002DA27DE60A964E9975F71FC22AB87DE912C25FFC2203063Q00E26ECD10846B03143Q00C8CCEDDB40FF83D4DC52FF83C4CC4CE6DAA0811903053Q00218BA380B903143Q00745709DC564C44EA524B109E734D09D34E185D8C03043Q00BE37386403143Q0075A0311C12F7B362AA2F0A53C7E65BA2255E4AB003073Q009336CF5C7E738303183Q002Q39306F0C730223303D2E71003334694D5A183C38644D2A03063Q001E6D51551D6D03153Q00DC7E59B437CABCCB7447A276FAE9F27C4DF6678EAE03073Q009C9F1134D656BE03153Q008DE0B0BEAFFBFD88ABFCA9FC8AFAB0B1B7AFECEDFD03043Q00DCCE8FDD030F3Q0047697A6C6F636B27732044752Q6D7903193Q00AF703D16DBD892B2783E0398E8C78B703457958CF58F7C232Q03073Q00B2E61D4D77B8AC03133Q00D8A71E137EFBB59A0B1676FFF0FE2E0E7AF5EC03063Q009895DE6A7B1703133Q00F329E44EB4D166D242B8DC21F30391C82BFB5A03053Q00D5BD469623031E3Q006C5A790A4E41343C4A4660486B407905561525581F153C244A527D07411C03043Q00682F351403153Q0080438C1EBD1BE378840FA84F87598C11A54FF21CD203063Q006FC32CE17CDC03153Q00FB490D71AABF98720560BFEBFC530D7EB2EB89175003063Q00CBB8266013CB031E3Q001A7C7443CF2D334D44DD2D335D54C3346A39109C6933574E8E1861744EDC03053Q00AE59131921031D3Q000C1D5F4CF6934B1B17415AB7A31E221F4B0EA1D74B011D126FE58A043D03073Q006B4F72322E97E7031E3Q001AA9B82B8B2DF7F43CB5A169AE2CBACD20E6E379CA0BB8CF2DE686398B3403083Q00A059C6D549EA59D7032C3Q006B7EB9FCC45C3180FBD65C3190EBC84568F4A8950842A4FBC9443197FFD14B79F4FFCB4C3186FBC94D70A7FB03053Q00A52811D49E03143Q00C6D6053127F1993C3635F1992C262BE8C0486B7303053Q004685B9685303143Q00274A4928C81005702FDA1005603FC4095C04729E03053Q00A96425244A03143Q002388AF520193E2640594B6102492AF5D19C7FB0003043Q003060E7C203133Q00EF48013809988786C95607231E988B96C5571703083Q00E3A83A6E4D79B8CF031E3Q005335B848F1F341E55339BE4CB8D576E54F39AC54F1FF64A87625FF11E08803083Q00C51B5CDF20D1BB1103263Q002B56C4F34377F3BB2856CFF7025DCFFE437CCCF6015ED7BB375AD0EF437BD6F60E4683AA520C03043Q009B633FA303193Q00ABDCB18CBA90C2E5A49EADC4A6C4AC80A0C4CF918381B8878903063Q00E4E2B1C1EDD903183Q001DBD33E737A463D231A337A610A52EEB2DF06EA616BC36E303043Q008654D04303193Q003AA1965D10B8C66816BF921C37B98B510AECCB1C34BE83591D03043Q003C73CCE603183Q00CE37FB71E42EAB44E229FF30C32FE67DFE7AA630CC35EF7F03043Q0010875A8B03183Q007D7916324D4038607115270E706D59791F7303145753662Q03073Q0018341466532E3403173Q00ED2231250CD06F15211CD06F053102C93661694FF62A2503053Q006FA44F4144031A3Q00EFD493DF2DFE86ED86CD3AAAE2CC8ED337AA8B99B0D62FEEC9CE03063Q008AA6B9E3BE4E031A3Q00E279D536513759FF71D62312070CC679DC771F632FD96DCE225E03073Q0079AB14A557324303263Q00EA39AB24A042F23DAA22F921C935BB37AD42E22DB43BA0428B789F37BA16CF37B776E8539F6C03063Q0062A658D956D903233Q00DAF76B139F9CC2F36A15C6FFF9FB7B00929CD2E3740C9F9CBBB65F0085C8FFF97741D103063Q00BC2Q961961E603123Q00F780510D1EADFE8852030BE89AAD4A0F01F403063Q008DBAE93F626C03163Q00DFEB34AE37F0E72DA565D2E521B424E5AA08A328FCF303053Q0045918A4CD6030E3Q0040DD888AAB1F73CAC9ADAA1B7DD603063Q007610AF2QE9DF03113Q00B9853CBFAEAF7C868532BEAEAF6886892C03073Q001DEBE455DB8EEB030F3Q000FD5B3D9377A265C36949EC87A433E03083Q00325DB4DABD172E4703133Q00ECA54B584BCE08EAA5494B41C808FAB156415D03073Q0028BEC43B2C24BC030D3Q000840CFA0F3730A7C61C9B9F76403073Q006D5C25BCD49A1D03173Q0030EAB7D7385403AF90C6325244DBB6C6341A20FAA9CE2803063Q003A648FC4A35103123Q002E4B2EA63B09C10F174324A67F6DF003175B03083Q006E7A2243C35F298503163Q0040BF5A58DB7AA35E4E9651B0564BD170F17F5FDB78A803053Q00B615D13B2A03173Q00815ED60820B2F763C00E35FE9342C81038FE9B56D71A2403063Q00DED737A57D4103183Q001AD8D50FF3CDAD7E29C2D25AD6D4E0473591EB1FF6C8F84703083Q002A4CB1A67A92A18D03173Q00938316DB787AE5BE00DD6D36819F08C36036968704C27503063Q0016C5EA65AE1903143Q0057617275672773205461726765742044752Q6D7903113Q001A31A4D7368BD68B2C33A09C52BADA8B3403083Q00E64D54C5BC16CFB7030F3Q00CE11C7F7CC95F13BF254E2E981ACE903083Q00559974A69CECC190031B3Q009FC46387D94087EF40B1E514E4D448A0F04080F540BEFD40F5B01D03063Q0060C4802DD38403173Q0011BD481FE1BAA6CE3C9B7A5DDBA3BDCC2CCD5F4ADFA2AD03083Q00B855ED1B3FB2CFD4030A3Q002B4B104C1C580552094E03043Q003F68396903083Q002082A8540D8EB75003043Q00246BE7C403043Q00739A8CA203043Q00E73DD5C203043Q002782135603043Q001369CD5D03043Q008727F0A403053Q005FC968BEE103043Q0081E4EFEB03043Q00AECFABA103063Q00FDF20CEAFDC503063Q00B78D9E6D9398026Q00144003053Q003C08F4183503043Q006C4C698603043Q00F9C4B8E503053Q00AE8BA5D18103083Q00417572615574696C030B3Q00466F724561636841757261030C3Q008B92D0ECE0365C649192CBE503083Q0018C3D382A1A6631003043Q00736F727403163Q00556E697447726F7570526F6C6573412Q7369676E656403043Q00756E697403043Q001871729303073Q00424C303CD8A3CB03043Q008EA757D803073Q0044DAE619933FAE027Q004003063Q00BD265255B3BF03053Q00D6CD4A332C026Q00594003083Q00746F6E756D62657203053Q006D617463682Q033Q00BF48A903053Q00179A2C829C03043Q0066696E6403043Q0003A7A4AA03063Q007371C6CDCE5603093Q0047579DF14F579EE75803043Q00822A38E803063Q00FEB436E4452B03063Q005F8AD544832003063Q0069706169727303063Q003E29B344733E03053Q00164A48C12303063Q003878F65F296D03043Q00384C1984025Q00C0724003093Q0053CEBE35CA51D7AE3403053Q00AF3EA1CB4603093Q0031D2D6003033CBC60103053Q00555CBDA373026Q00694003093Q002EBE3F2D39993E313D03043Q005849CC50030A3Q002D96035226D71B8D195203063Q00BA4EE370264903143Q006E616D65706C6174654C556E697473436163686503193Q006E616D65706C6174654C556E69747343616368654672616D6503053Q00DA65DC787603063Q001A9C379D3533030B3Q00696E697469616C697A656403153Q00BCF437E09D62B3FD38ED9D62A5F631E68F7FBEF43203063Q0030ECB876B9D803153Q00CB9C7A15F004C99C6315F001CB94630FEE10C1987303063Q005485DD3750AF03173Q0093C60983F86C91C61083F86993CE1099F57990C81283E303063Q003CDD8744C6A703173Q00C292D9A76BF7C982CBA070FCCB93C7A76BEACF9FD4A66603063Q00B98EDD98E32203073Q0077CB72EC463DE303073Q009738A5379A2353031F3Q0048616E646C654C4E616D65706C617465556E6974734361636865412Q64656403213Q0048616E646C654C4E616D65706C617465556E697473436163686552656D6F766564030C3Q004C52616E6765436865636B4C030A3Q00EA51B3BB47E4B514E7E203063Q00D583252QD67D026Q001040030A3Q002F3F20B2BB757C72EDB603053Q0081464B45DF030A3Q004FDFF6E426BE1393A1BF03063Q008F26AB93891C030A3Q00D996BCFE59B58784D0EE03073Q00B4B0E2D9936383030A3Q00DAAD2A0A89EA7B5485E103043Q0067B3D94F026Q001C40030A3Q0043A319D81BDFF119E54D03073Q00C32AD77CB521EC030A3Q00044D32337FA95A0F656803063Q00986D39575E45030A3Q00F0C30FAEE48107F8AF8E03083Q00C899B76AC3DEB234026Q002E40030A3Q003BF78D30130B62B5DC6803063Q003A5283E85D29026Q003440030A3Q008A43D518076DD705864D03063Q005FE337B0753D03083Q00116A2646F1402D7603053Q00CB781E432B026Q003E4003093Q00F83148E283A8761FB703053Q00B991452D8F030A3Q00830B1CAB86D82Q4BF08503053Q00BCEA7F79C6025Q0080414003093Q003126168E626340DA6103043Q00E3585273030A3Q004A0BBFAA58211B48ECF003063Q0013237FDAC762026Q00444003093Q0015EF0FEF46AF53B64903043Q00827C9B6A030A3Q00DCDFF3A2F9A52EE98C9303083Q00DFB5AB96CFC3961C025Q00804640030B3Q00452EE6A3531D6BB5FF5A1503053Q00692C5A83CE026Q004940030A3Q00F6F4B7B4526DADB8E0EC03063Q005E9F80D2D968026Q004E40030A3Q0059ED03B2052BA82806AC03083Q001A309966DF3F1F99025Q00805140030A3Q000B54E8FE5813B8A1551803043Q009362208D026Q005440030A3Q001157E6C75C05184912BA03073Q002B782383AA663603053Q00706169727303093Q00756E6974506C61746503083Q00756E69744E616D6503063Q00756E6974496403053Q0097C3C0CCD003073Q0025D3B6ADA1A9C103133Q00556E6974412Q66656374696E67436F6D626174030C3Q00556E69745265616374696F6E03063Q00E7364CC02D6903073Q00D9975A2DB9481B03063Q00D370E60B53D103053Q0036A31C8772030B3Q00556E6974496E5061727479030C3Q003CDA4F854B6B3CDA4F854B6B03063Q001F48BB3DE22E030A3Q00556E6974496E52616964030C3Q00D70751D5426A30C21444D75303073Q0044A36623B2271E030A3Q00556E69744973556E6974030C3Q00AA71C8C006A19710AC77DFD303083Q0071DE10BAA763D5E303063Q003E02FAEF2B1C03043Q00964E6E9B026Q00204003063Q0095C926F8A10C03083Q0020E5A54781C47EDF03063Q00D788D68684C103063Q00B5A3E9A42QE103063Q0040873F6E559903043Q001730EB5E03063Q0068DBCA5A522703073Q00B21CBAB83D375303063Q00D0CC553BF71A03073Q0095A4AD275C926E03063Q00546172676574030C3Q00556E697473496E4D656C2Q65030C3Q00556E697473496E52616E676503143Q00496E74652Q727570744C4672616D65436163686503053Q00D51531323F03063Q007B9347707F7A03143Q00496E74652Q727570744C556E6974734361636865030C3Q004B69636B5370652Q6C49647303163Q00C5C3967454DED8926569C2C19B464EC5D9877D4FDFD903053Q0026ACADE211031C3Q00783F05DB72221CCA613D0FCE7E2513CC653002C1683D13DC79301EDB03043Q008F2D714C031B3Q008D963508878B2C192Q943F1D8B8C231F909932129D94230F8C972C03043Q005C2QD87C031D3Q006E1C8574C26802896CD178139F74C2781A8D6ED37E1E9375CD7F13986503053Q009D3B52CC20031C3Q000D10CACED6D9E3941412C0DBDADEEC94150ECCCDCCD8EC820C1FD1CE03083Q00D1585E839A898AB3031B3Q001D8FED4821100107048DE75D2D170E070591EB4B3B110E111C8EF403083Q004248C1A41C7E4351031D3Q00D202816C1945D70984740557D418977D0B46C81B8D6A1943D708896C2Q03063Q0016874CC8384603143Q00B81ED11062D2BD15D4087EC0BE04C71769C0BF0403063Q0081ED5098443D03133Q0064862DC7232468748428D03D246C6E9B30DC2C03073Q003831C864937C77031A3Q00F91096C4F30D8FD5E0129CD1FF0A80D9E20A9AC2FE0B8FC4E91A03043Q0090AC5EDF03183Q0011218B731B3C926208238166173B9D74112C8162012B876303043Q0027446FC203203Q00E388CEF34684E683CBEB5A96E592D8E95683E98FC9F35C85E493D7F35095FA8303063Q00D7B6C687A71903073Q00A247CF5E8847FE03043Q0028ED298A03053Q0025C223AB8D03053Q00E863B042C603163Q00C13804037C88F728ED3331336B89F838E9073A07768803083Q004C8C4148661BED9903083Q005549506172656E7403083Q0065D423C2D300AA4F03073Q00DE2ABA76B2B761002F062Q0012343Q00013Q00206Q000200122Q000100013Q00202Q00010001000300122Q000200013Q00202Q00020002000400122Q000300053Q00062Q0003000A0001000100049E3Q000A000100122Q000300063Q00203E00040003000700122Q000500083Q00203E00050005000900122Q000600083Q00203E00060006000A0006E300073Q000100062Q00FD3Q00064Q00FD8Q00FD3Q00044Q00FD3Q00014Q00FD3Q00024Q00FD3Q00054Q002F0008000A3Q00122Q000A000B6Q000B3Q00024Q000C00073Q00122Q000D000D3Q00122Q000E000E6Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00103Q00122Q000E00116Q000C000E000200202Q000B000C000F00102Q000A000C000B4Q000B3Q000A4Q000C00073Q00122Q000D00133Q00122Q000E00146Q000C000E000200202Q000B000C00154Q000C00073Q00122Q000D00163Q00122Q000E00176Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00183Q00122Q000E00196Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D001B3Q00122Q000E001C6Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D001D3Q00122Q000E001E6Q000C000E000200202Q000B000C001F4Q000C00073Q00122Q000D00203Q00122Q000E00216Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D00223Q00122Q000E00236Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00243Q00122Q000E00256Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00263Q00122Q000E00276Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00283Q00122Q000E00296Q000C000E000200202Q000B000C000F00102Q000A0012000B4Q000B3Q00084Q000C00073Q00122Q000D002B3Q00122Q000E002C6Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D002D3Q00122Q000E002E6Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D002F3Q00122Q000E00304Q0042000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D00313Q00122Q000E00326Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00333Q00122Q000E00344Q0042000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00353Q00122Q000E00366Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00373Q00122Q000E00384Q0079000C000E00020020D2000B000C000F2Q00AB000C00073Q00122Q000D00393Q00122Q000E003A6Q000C000E000200202Q000B000C001500102Q000A002A000B00122Q000B003B6Q000C00073Q00122Q000D003C3Q00122Q000E003D4Q0074000C000E4Q00A9000B3Q000200202Q000C000B003E4Q000E00073Q00122Q000F003F3Q00122Q001000406Q000E00106Q000C3Q000100202Q000C000B003E4Q000E00073Q00122Q000F00413Q001209011000424Q0019010E00106Q000C3Q000100202Q000C000B00434Q000E00073Q00122Q000F00443Q00122Q001000456Q000E001000020006E3000F0001000100022Q00FD3Q00074Q00FD3Q000A4Q00B0000C000F00010006E3000C0002000100022Q00FD3Q000A4Q00FD3Q00073Q0006E3000D0003000100022Q00FD3Q000A4Q00FD3Q00073Q0006E3000E0004000100022Q00FD3Q00074Q00FD3Q000A3Q0006E3000F0005000100022Q00FD3Q00074Q00FD3Q000A3Q00122Q001000463Q00122Q001100463Q00203E0011001100470006D7001100AF0001000100049E3Q00AF00012Q008300115Q0010A70010004700110012B80010000B3Q00202Q0010001000484Q001100073Q00122Q001200493Q00122Q0013004A6Q0011001300024Q00100010001100122Q0011000F3Q00122Q0012004B6Q0012000100020026B5001200BE0001000F00049E3Q00BE00010012090111004C3Q00049E3Q00BF00012Q00FD001100123Q000E0C014D00C20001001100049E3Q00C200010012090111004D4Q008300133Q001D0030970013004E004F00302Q00130050004F00302Q00130051004F00302Q00130052004F00302Q00130053004F00302Q00130054004F00302Q00130055004F00302Q00130056004F00302Q00130057004F00302Q00130058004F00302Q00130059004F00302Q0013005A004F00302Q0013005B004F00302Q0013005C004F00302Q0013005D004F00302Q0013005E004F00302Q0013005F004F00302Q00130060004F00302Q00130061004F00302Q00130062004F00302Q00130063004F00302Q00130064004F00302Q00130065004F00302Q00130066004F00302Q00130067004F00302Q00130068004F00302Q00130069004F00302Q0013006A004F00302Q0013006B004F00302Q0013006C004F00302Q0013006D004F00302Q0013006E004F00302Q0013006F004F00302Q00130070004F00302Q00130071004F00302Q00130072004F00302Q00130073004F00302Q00130074004F00302Q00130075004F00302Q00130076004F00302Q00130077004F00302Q00130078004F00302Q00130079004F00302Q0013007A004F00302Q0013007B004F00302Q0013007C004F00302Q0013007D004F00302Q0013007E004F00302Q0013007F004F00302Q00130080004F00302Q00130081004F4Q00143Q00234Q001500073Q00122Q001600823Q00122Q001700836Q00150017000200202Q00140015004F4Q001500073Q00122Q001600843Q00122Q001700856Q00150017000200202Q00140015004F4Q001500073Q00122Q001600863Q00122Q001700876Q00150017000200202Q00140015004F00302Q00140088004F00302Q00140089004F4Q001500073Q00122Q0016008A3Q00122Q0017008B6Q00150017000200202Q00140015004F00302Q0014008C004F4Q001500073Q00122Q0016008D3Q00122Q0017008E6Q00150017000200202Q00140015004F2Q00FD001500073Q0012F70016008F3Q00122Q001700906Q00150017000200202Q00140015004F4Q001500073Q00122Q001600913Q00122Q001700926Q00150017000200202Q00140015004F4Q001500073Q00122Q001600933Q00122Q001700946Q00150017000200202Q00140015004F00302Q00140095004F00302Q00140096004F4Q001500073Q00122Q001600973Q00122Q001700986Q00150017000200202Q00140015004F4Q001500073Q00122Q001600993Q00122Q0017009A6Q00150017000200202Q00140015004F4Q001500073Q00122Q0016009B3Q00122Q0017009C6Q00150017000200202Q00140015004F4Q001500073Q00122Q0016009D3Q00122Q0017009E6Q00150017000200202Q00140015004F4Q001500073Q00122Q0016009F3Q00122Q001700A06Q00150017000200202Q00140015004F00302Q001400A1004F4Q001500073Q00122Q001600A23Q00122Q001700A36Q00150017000200202Q00140015004F00302Q001400A4004F4Q001500073Q00122Q001600A53Q00122Q001700A66Q00150017000200202Q00140015004F00302Q001400A7004F00302Q001400A8004F00302Q001400A9004F4Q001500073Q00122Q001600AA3Q00122Q001700AB6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600AC3Q00122Q001700AD6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600AE3Q00122Q001700AF6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600B03Q00122Q001700B16Q00150017000200202Q00140015004F4Q001500073Q00122Q001600B23Q00122Q001700B36Q0015001700020020D200140015004F2Q001B001500073Q00122Q001600B43Q00122Q001700B56Q00150017000200202Q00140015004F4Q001500073Q00122Q001600B63Q00122Q001700B76Q00150017000200202Q00140015004F4Q001500073Q00122Q001600B83Q00122Q001700B96Q00150017000200202Q00140015004F4Q001500073Q00122Q001600BA3Q00122Q001700BB6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600BC3Q00122Q001700BD6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600BE3Q00122Q001700BF6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600C03Q00122Q001700C16Q00150017000200202Q00140015004F4Q001500073Q00122Q001600C23Q00122Q001700C36Q00150017000200202Q00140015004F4Q001500073Q00122Q001600C43Q00122Q001700C56Q00150017000200202Q00140015004F4Q001500073Q00122Q001600C63Q00122Q001700C76Q00150017000200202Q00140015004F00302Q001400C8004F4Q001500073Q00122Q001600C93Q00122Q001700CA6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600CB3Q00122Q001700CC6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600CD3Q00122Q001700CE6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600CF3Q00122Q001700D06Q00150017000200202Q00140015004F4Q001500073Q00122Q001600D13Q00122Q001700D26Q00150017000200202Q00140015004F4Q001500073Q00122Q001600D33Q00122Q001700D46Q0015001700020020D200140015004F2Q005B001500073Q00122Q001600D53Q00122Q001700D66Q00150017000200202Q00140015004F4Q001500073Q00122Q001600D73Q00122Q001700D86Q00150017000200202Q00140015004F4Q001500073Q00122Q001600D93Q00122Q001700DA6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600DB3Q00122Q001700DC6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600DD3Q00122Q001700DE6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600DF3Q00122Q001700E06Q00150017000200202Q00140015004F4Q001500073Q00122Q001600E13Q00122Q001700E26Q00150017000200202Q00140015004F4Q001500073Q00122Q001600E33Q00122Q001700E46Q00150017000200202Q00140015004F4Q001500073Q00122Q001600E53Q00122Q001700E66Q00150017000200202Q00140015004F4Q001500073Q00122Q001600E73Q00122Q001700E86Q00150017000200202Q00140015004F4Q001500073Q00122Q001600E93Q00122Q001700EA6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600EB3Q00122Q001700EC6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600ED3Q00122Q001700EE6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600EF3Q00122Q001700F06Q00150017000200202Q00140015004F4Q001500073Q00122Q001600F13Q00122Q001700F26Q00150017000200202Q00140015004F4Q001500073Q00122Q001600F33Q00122Q001700F46Q00150017000200202Q00140015004F2Q00FD001500073Q0012BD001600F53Q00122Q001700F66Q00150017000200202Q00140015004F4Q001500073Q00122Q001600F73Q00122Q001700F86Q00150017000200202Q00140015004F4Q001500073Q00122Q001600F93Q00122Q001700FA6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600FB3Q00122Q001700FC6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600FD3Q00122Q001700FE6Q00150017000200202Q00140015004F4Q001500073Q00122Q001600FF3Q00122Q00172Q00015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q0016002Q012Q00122Q00170002015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160003012Q00122Q00170004015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160005012Q00122Q00170006015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160007012Q00122Q00170008015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160009012Q00122Q0017000A015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q0016000B012Q00122Q0017000C015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q0016000D012Q00122Q0017000E015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q0016000F012Q00122Q00170010015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160011012Q00120901170012013Q00AA0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160013012Q00122Q00170014015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160015012Q00122Q00170016015Q0015001700024Q001600016Q00140015001600122Q00150017015Q001600016Q0014001500164Q001500073Q00122Q00160018012Q00122Q00170019015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q0016001A012Q00122Q0017001B015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q0016001C012Q00122Q0017001D015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q0016001E012Q00122Q0017001F015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160020012Q00122Q00170021015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160022012Q00122Q00170023015Q0015001700024Q001600016Q0014001500164Q001500073Q00122Q00160024012Q00122Q00170025015Q0015001700024Q001600073Q00122Q00170026012Q00122Q00180027015Q0016001800024Q001700073Q00122Q00180028012Q00122Q00190029015Q0017001900024Q001800073Q00122Q0019002A012Q00122Q001A002B015Q0018001A00020002B9001900064Q00CB001A5Q00122Q001B000F3Q00122Q001C004C6Q001C0011001C00122Q001D004C3Q00042Q001B00DD0201001209011F000F4Q002Q012000203Q0012090121000F3Q0006FE001F00A70201002100049E3Q00A702010012090121000F3Q0006FE001E00B30201002100049E3Q00B302012Q00FD002100073Q0012090122002C012Q0012090123002D013Q00790021002300020006DE002000C40201002100049E3Q00C402010012090121002E012Q00066A001100BE0201002100049E3Q00BE02012Q00FD002100073Q00126B0022002F012Q00122Q00230030015Q0021002300024Q0022001E6Q00210021002200062Q002000C40201002100049E3Q00C402012Q00FD002100073Q00124000220031012Q00122Q00230032015Q0021002300024Q0022001E6Q00200021002200122Q00210033012Q00121400220034015Q0021002100224Q002200206Q002300073Q00122Q00240035012Q00122Q00250036015Q0023002500024Q002400243Q0006E3002500070001000A2Q00FD3Q00134Q00FD3Q00154Q00FD3Q00174Q00FD3Q00164Q00FD3Q00184Q00FD3Q00104Q00FD3Q00194Q00FD3Q00204Q00FD3Q00074Q00FD3Q001A4Q00B000210025000100049E3Q00DB020100049E3Q00A702012Q0075001F5Q0004F1001B00A5020100122Q001B00083Q001209011C0037013Q0038001B001B001C2Q00FD001C001A3Q0002B9001D00084Q00AC001B001D00014Q001B001B6Q001C001A3Q00122Q001D000F3Q00062Q001D00160301001C00049E3Q0016030100122Q001C0038012Q0012E6001D004C6Q001D001A001D00122Q001E0039015Q001D001D001E4Q001C000200024Q001D00073Q00122Q001E003A012Q00122Q001F003B015Q001D001F000200062Q001C00FD0201001D00049E3Q00FD02012Q0022001C001A3Q001209011D004C3Q0006FE001C00FD0201001D00049E3Q00FD0201001209011C004C4Q0038001C001A001C001209011D0039013Q0038001B001C001D00049E3Q0016030100122Q001C0038012Q0012EC001D004C6Q001D001A001D00122Q001E0039015Q001D001D001E4Q001C000200024Q001D00073Q00122Q001E003C012Q00122Q001F003D015Q001D001F000200062Q001C000E0301001D00049E3Q000E0301001209011C004C4Q0038001C001A001C001209011D0039013Q0038001B001C001D00049E3Q001603012Q0022001C001A3Q001209011D004C3Q000669001D00160301001C00049E3Q00160301001209011C003E013Q0038001C001A001C001209011D0039013Q0038001B001C001D001209011C000F3Q00066D001B004403013Q00049E3Q004403012Q00FD001D00073Q001209011E003F012Q001209011F0040013Q0079001D001F00020006FE001B00210301001D00049E3Q00210301001209011C0041012Q00049E3Q00440301001209011D000F4Q002Q011E001E3Q001209011F000F3Q0006FE001D00230301001F00049E3Q0023030100122Q001F0042012Q0012E8002000013Q00122Q00210043015Q0020002000214Q0021001B6Q002200073Q00122Q00230044012Q00122Q00240045015Q002200246Q00208Q001F3Q00022Q00FD001E001F3Q00066D001E004403013Q00049E3Q0044030100122Q001F00013Q0012CA00200046015Q001F001F00204Q0020001B6Q002100073Q00122Q00220047012Q00122Q00230048015Q002100236Q001F3Q000200062Q001F004103013Q00049E3Q004103012Q00FD001C001E3Q00049E3Q004403012Q00FD001C001E3Q00049E3Q0044030100049E3Q002303010006E3001D0009000100062Q00FD3Q00144Q00FD3Q00074Q00FD3Q00154Q00FD3Q00174Q00FD3Q00164Q00FD3Q00183Q001227001E000F6Q001F00016Q002000073Q00122Q00210049012Q00122Q0022004A015Q0020002200024Q002100073Q00122Q0022004B012Q00122Q0023004C015Q002100234Q00A6001F3Q000100122Q0020004D013Q00FD0021001F4Q002500200002002200049E3Q007D03012Q00FD002500073Q0012090126004E012Q0012090127004F013Q00790025002700020006FE0024006C0301002500049E3Q006C03010012090125000F3Q0006FE001E007D0301002500049E3Q007D03012Q00FD0025001D4Q0035002600073Q00122Q00270050012Q00122Q00280051015Q00260028000200122Q00270052015Q0025002700024Q001E00253Q00044Q007D03012Q00FD002500073Q00120901260053012Q00120901270054013Q00790025002700020006FE0024007D0301002500049E3Q007D03010012090125000F3Q0006FE001E007D0301002500049E3Q007D03012Q00FD0025001D4Q0099002600073Q00122Q00270055012Q00122Q00280056015Q00260028000200122Q00270057015Q0025002700024Q001E00253Q0006630020005A0301000200049E3Q005A030100122Q002000464Q000A01213Q00024Q002200073Q00122Q00230058012Q00122Q00240059015Q0022002400024Q00210022001C4Q002200073Q00122Q0023005A012Q00122Q0024005B015Q0022002400022Q009D00210022001E0010FF00200047002100122Q002000463Q00122Q0021005C012Q00122Q002200463Q00122Q0023005C015Q00220022002300062Q002200940301000100049E3Q009403012Q008300226Q009D00200021002200127F002000463Q00122Q0021005D012Q00122Q002200463Q00122Q0023005D015Q00220022002300062Q002200A20301000100049E3Q00A2030100122Q0022003B4Q00AF002300073Q00122Q0024005E012Q00122Q0025005F015Q002300256Q00223Q00022Q009D00200021002200129A002000463Q00122Q0021005D015Q00200020002100122Q00210060015Q00200020002100062Q002000F10301000100049E3Q00F103010012090120000F3Q0012090121000F3Q0006FE002000C10301002100049E3Q00C1030100122Q002100463Q0012840022005D015Q00210021002200202Q00210021003E4Q002300073Q00122Q00240061012Q00122Q00250062015Q002300256Q00213Q000100122Q002100463Q00122Q0022005D013Q003800210021002200209800210021003E4Q002300073Q00122Q00240063012Q00122Q00250064015Q002300256Q00213Q000100122Q0020004C3Q0012090121004C3Q0006FE002100D70301002000049E3Q00D7030100122Q002100463Q0012840022005D015Q00210021002200202Q00210021003E4Q002300073Q00122Q00240065012Q00122Q00250066015Q002300256Q00213Q000100122Q002100463Q00122Q0022005D013Q003800210021002200209800210021003E4Q002300073Q00122Q00240067012Q00122Q00250068015Q002300256Q00213Q000100122Q0020003E012Q0012090121003E012Q0006FE002000AB0301002100049E3Q00AB030100122Q002100463Q00124B0022005D015Q00210021002200202Q0021002100434Q002300073Q00122Q00240069012Q00122Q0025006A015Q0023002500020006E30024000A000100052Q00FD3Q00074Q00FD3Q00184Q00FD3Q00154Q00FD3Q00174Q00FD3Q00164Q007000210024000100122Q002100463Q00122Q0022005D015Q00210021002200122Q00220060015Q002300016Q00210022002300044Q00F1030100049E3Q00AB03010006E30020000B000100012Q00FD3Q00073Q0012560020006B012Q0002B90020000C3Q00120D0120006C012Q00122Q002000463Q00122Q0021006D012Q00122Q002200463Q00122Q0023006D015Q00220022002300062Q002200FE0301000100049E3Q00FE03012Q008300226Q009D0020002100222Q001201203Q00134Q002100073Q00122Q0022006E012Q00122Q0023006F015Q00210023000200122Q00220070015Q0020002100224Q002100073Q00122Q00220071012Q00122Q00230072015Q00210023000200122Q0022002E015Q0020002100224Q002100073Q00122Q00220073012Q00122Q00230074015Q00210023000200122Q0022002E015Q0020002100224Q002100073Q00122Q00220075012Q00122Q00230076015Q00210023000200122Q0022002E015Q0020002100224Q002100073Q00122Q00220077012Q00122Q00230078015Q00210023000200122Q00220079015Q0020002100224Q002100073Q00122Q0022007A012Q00122Q0023007B015Q00210023000200122Q00220079015Q0020002100224Q002100073Q00122Q0022007C012Q00122Q0023007D015Q00210023000200122Q00220079015Q0020002100224Q002100073Q00122Q0022007E012Q00122Q0023007F015Q00210023000200122Q00220080015Q0020002100224Q002100073Q00122Q00220081012Q00122Q00230082015Q00210023000200122Q00220083015Q0020002100224Q002100073Q00122Q00220084012Q00122Q00230085015Q00210023000200122Q0022004D6Q0020002100224Q002100073Q00122Q00220086012Q00122Q00230087015Q00210023000200122Q00220088015Q0020002100224Q002100073Q00122Q00220089012Q00122Q0023008A015Q00210023000200122Q00220088015Q0020002100224Q002100073Q00122Q0022008B012Q00122Q0023008C015Q00210023000200122Q0022008D015Q0020002100224Q002100073Q0012C40022008E012Q00122Q0023008F015Q00210023000200122Q0022008D015Q0020002100224Q002100073Q00122Q00220090012Q00122Q00230091015Q00210023000200122Q00220092013Q00C60020002100224Q002100073Q00122Q00220093012Q00122Q00230094015Q00210023000200122Q00220092015Q0020002100224Q002100073Q00122Q00220095012Q00122Q00230096013Q001000210023000200122Q00220097015Q0020002100224Q002100073Q00122Q00220098012Q00122Q00230099015Q00210023000200122Q0022009A015Q0020002100222Q004E002100073Q00122Q0022009B012Q00122Q0023009C015Q00210023000200122Q0022009D015Q0020002100224Q002100073Q00122Q0022009E012Q00122Q0023009F015Q0021002300020012A4002200A0015Q0020002100224Q002100073Q00122Q002200A1012Q00122Q002300A2015Q00210023000200122Q002200A3015Q0020002100224Q002100073Q00122Q002200A4012Q001209012300A5013Q007900210023000200120901220041013Q009D0020002100220006E30021000D000100022Q00FD3Q00204Q00FD3Q00074Q00FC00225Q00122Q0023000F3Q00122Q0024000F3Q00122Q002500463Q00122Q0026005C015Q00250025002600062Q002500900401000100049E3Q009004012Q008300255Q00066D0025002805013Q00049E3Q0028050100122Q002600A6013Q00FD002700254Q002500260002002800049E3Q00260501001209012B000F4Q002Q012C002C3Q001209012D000F3Q0006FE002B00980401002D00049E3Q00980401001209012D00A7013Q0038002C002A002D00066D002C002605013Q00049E3Q00260501001209012D000F4Q002Q012E00323Q0012090133000F3Q0006FE002D00C00401003300049E3Q00C00401001209013300A8013Q001C002E002A003300122Q00330042012Q00122Q003400A9015Q0034002A00344Q0033000200024Q0033002200334Q003400013Q00062Q003300BE0401003400049E3Q00BE04012Q002Q013300333Q0006B6002E00BD0401003300049E3Q00BD040100122Q003300013Q0012E900340046015Q0033003300344Q0034002E6Q003500073Q00122Q003600AA012Q00122Q003700AB015Q003500376Q00333Q00024Q003400343Q00062Q003300BE0401003400049E3Q00BE04012Q00C3002F6Q0005012F00013Q001209012D004C3Q0012090133004C3Q0006FE002D00FB0401003300049E3Q00FB040100122Q003300AC013Q00FD0034002C4Q00F000330002000200066D003300DB04013Q00049E3Q00DB040100122Q003300AD013Q00A8003400073Q00122Q003500AE012Q00122Q003600AF015Q0034003600024Q0035002C6Q00330035000200062Q003300DB04013Q00049E3Q00DB040100122Q003300AD013Q0055003400073Q00122Q003500B0012Q00122Q003600B1015Q0034003600024Q0035002C6Q00330035000200122Q00340070012Q00062Q003300040001003400049E3Q00DE04012Q00FD0030002F3Q00049E3Q00DF04012Q00C300306Q0005013000013Q00122Q003300B2013Q00AE003400073Q00122Q003500B3012Q00122Q003600B4015Q003400366Q00333Q000200062Q003100FA0401003300049E3Q00FA040100122Q003300B5013Q00AE003400073Q00122Q003500B6012Q00122Q003600B7015Q003400366Q00333Q000200062Q003100FA0401003300049E3Q00FA040100122Q003300B8013Q00D1003400073Q00122Q003500B9012Q00122Q003600BA015Q0034003600024Q003500073Q00122Q003600BB012Q00122Q003700BC015Q003500376Q00333Q00024Q003100333Q001209012D003E012Q0012090133003E012Q0006FE002D00A10401003300049E3Q00A10401000618003200040501003000049E3Q000405012Q00FD003300214Q00FD0034002C4Q00F00033000200022Q00FD003200333Q00066D002C002605013Q00049E3Q0026050100066D0030002605013Q00049E3Q002605010012090133000F3Q0012090134000F3Q0006FE003300090501003400049E3Q000905010006D7003100130501000100049E3Q00130501001209013400BD012Q00063A003200030001003400049E3Q0013050100066D002F001705013Q00049E3Q001705010012090134004C4Q00F50034002300340012090135000F4Q00F50023003400350006D70031001E0501000100049E3Q001E050100120901340092012Q00063A003200030001003400049E3Q001E050100066D002F002605013Q00049E3Q002605010012090134004C4Q00F500240024003400049E3Q0026050100049E3Q0009050100049E3Q0026050100049E3Q00A1040100049E3Q0026050100049E3Q00980401000663002600960401000200049E3Q0096040100120901260041012Q00128F002700AD015Q002800073Q00122Q002900BE012Q00122Q002A00BF015Q0028002A00024Q002900073Q00122Q002A00C0012Q00122Q002B00C1015Q0029002B6Q00273Q000200066D0027005305013Q00049E3Q0053050100122Q002700AD013Q00C2002800073Q00122Q002900C2012Q00122Q002A00C3015Q0028002A00024Q002900073Q00122Q002A00C4012Q00122Q002B00C5015Q0029002B6Q00273Q000200122Q00280070012Q00066A002700530501002800049E3Q005305010012090127000F4Q002Q012800283Q0012090129000F3Q0006FE002900440501002700049E3Q004405012Q00FD002900214Q005F002A00073Q00122Q002B00C6012Q00122Q002C00C7015Q002A002C6Q00293Q00024Q002800293Q00062Q0028005305013Q00049E3Q005305012Q00FD002600283Q00049E3Q0053050100049E3Q0044050100122Q002700463Q0012090128006D013Q003800270027002800066D0027007105013Q00049E3Q007105010012090127000F3Q0012090128004C3Q0006FE002700620501002800049E3Q0062050100122Q002800463Q00125C0029006D015Q00280028002900122Q002900C8015Q00280029002600044Q007105010012090128000F3Q0006FE002700590501002800049E3Q0059050100122Q002800463Q0012080029006D015Q00280028002900122Q002900C9015Q00280029002300122Q002800463Q00122Q0029006D015Q00280028002900122Q002900CA015Q00280029002400122Q0027004C3Q00049E3Q0059050100122Q002700463Q001288002800CB012Q00122Q002900463Q00122Q002A00CB015Q00290029002A00062Q0029007E0501000100049E3Q007E050100122Q0029003B4Q00AF002A00073Q00122Q002B00CC012Q00122Q002C00CD015Q002A002C6Q00293Q00022Q009D00270028002900127F002700463Q00122Q002800CE012Q00122Q002900463Q00122Q002A00CE015Q00290029002A00062Q002900870501000100049E3Q008705012Q008300296Q009D00270028002900127F002700463Q00122Q002800CF012Q00122Q002900463Q00122Q002A00CF015Q00290029002A00062Q002900900501000100049E3Q009005012Q008300296Q009D0027002800290012280027000B3Q00202Q0027002700484Q002800073Q00122Q002900D0012Q00122Q002A00D1015Q0028002A00024Q0027002700284Q002700273Q00122Q002800463Q00122Q002900CB013Q003800280028002900120901290060013Q00380028002800290006D7002800150601000100049E3Q0015060100122Q002800463Q00124D002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00D2012Q00122Q002C00D3015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00D4012Q00122Q002C00D5015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00D6012Q00122Q002C00D7015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00D8012Q00122Q002C00D9015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00DA012Q00122Q002C00DB015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00DC012Q00122Q002C00DD015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00DE012Q00122Q002C00DF015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00E0012Q00122Q002C00E1015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00E2012Q00122Q002C00E3015Q002A002C6Q00283Q0001001244002800463Q00122Q002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00E4012Q00122Q002C00E5015Q002A002C6Q00283Q000100122Q002800463Q001284002900CB015Q00280028002900202Q00280028003E4Q002A00073Q00122Q002B00E6012Q00122Q002C00E7015Q002A002C6Q00283Q000100122Q002800463Q00122Q002900CB013Q00380028002800290020D90028002800432Q00FD002A00073Q001209012B00E8012Q001209012C00E9013Q0079002A002C00020006E3002B000E000100022Q00FD3Q00074Q00FD3Q00274Q00910028002B000100122Q002800463Q00122Q002900CB015Q00280028002900122Q00290060015Q002A00016Q00280029002A00122Q0028003B4Q0002002900073Q00122Q002A00EA012Q00122Q002B00EB015Q0029002B00024Q002A00073Q00122Q002B00EC012Q00122Q002C00ED015Q002A002C000200122Q002B00EE015Q0028002B00020020D90029002800432Q00FD002B00073Q001209012C00EF012Q001209012D00F0013Q0079002B002D00020006E3002C000F000100072Q00FD3Q000E4Q00FD3Q000F4Q00FD3Q000C4Q00FD3Q000D4Q00FD3Q00074Q00FD3Q000A4Q00FD3Q00214Q00B00029002C00012Q003F3Q00013Q00103Q00023Q00026Q00F03F026Q00704002264Q000A00025Q00122Q000300016Q00045Q00122Q000500013Q00042Q0003002100012Q000F01076Q002E000800026Q000900016Q000A00026Q000B00036Q000C00046Q000D8Q000E00063Q00202Q000F000600014Q000C000F6Q000B3Q00024Q000C00036Q000D00046Q000E00016Q000F00016Q000F0006000F00102Q000F0001000F4Q001000016Q00100006001000102Q00100001001000202Q0010001000014Q000D00106Q000C8Q000A3Q000200202Q000A000A00024Q0009000A6Q00073Q00010004F10003000500012Q000F010300054Q00FD000400024Q000F000300044Q00A500036Q003F3Q00017Q00063Q0003143Q00890F8A4D9A8D7A869C048E5A809A6B959B0F8E5003083Q00D4D943CB142QDF25028Q00030B3Q00426967576967734461746103083Q004D652Q736167657303063Q00536F756E647302124Q00BF00025Q00122Q000300013Q00122Q000400026Q00020004000200062Q000100110001000200049E3Q00110001001209010200033Q0026B5000200070001000300049E3Q000700012Q000F010300013Q00206100030003000400302Q0003000500034Q000300013Q00202Q00030003000400302Q00030006000300044Q0011000100049E3Q000700012Q003F3Q00017Q000E3Q00028Q00026Q00F03F030E3Q005F42696757696773482Q6F6B6564030E3Q00682Q6F6B73656375726566756E63030D3Q00426967576967734C6F61646572030B3Q008988A6D69788BBC1BB8AAD03043Q00B2DAEDC82Q0103083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q001308D583F1D7AE0E22DDA6FD03073Q00DD5161B2D498B003083Q00C0E20EE81BCAE20E03053Q007AAD877D9B00353Q001209012Q00014Q003Q0100033Q0026B53Q001F0001000200049E3Q001F000100066D0001003400013Q00049E3Q0034000100066D0002003400013Q00049E3Q003400012Q000F01045Q00203E0004000400030006D7000400340001000100049E3Q00340001001209010400013Q0026B50004000D0001000100049E3Q000D000100122Q000500043Q0012E7000600056Q000700013Q00122Q000800063Q00122Q000900076Q0007000900020006E300083Q000100032Q000F012Q00014Q00FD3Q00034Q000F017Q00B00005000800012Q000F01055Q00308900050003000800049E3Q0034000100049E3Q000D000100049E3Q003400010026B53Q00020001000100049E3Q0002000100122Q000400093Q00208000040004000A4Q000500013Q00122Q0006000B3Q00122Q0007000C6Q000500076Q00043Q00054Q000200056Q000100046Q00043Q00014Q000500013Q00122Q0006000D3Q00122Q0007000E6Q0005000700024Q00068Q0004000500064Q000300043Q00124Q00023Q00044Q000200012Q003F3Q00013Q00013Q001F3Q00028Q00030F3Q0094BCE1E7BFB2F5EF9BB0F5C3B7B2E303043Q00B0D6D58603053Q007461626C6503063Q00696E7365727403083Q006D652Q736167657303093Q00E0A4BBD1BB4258F9BD03073Q003994CDD6B4C83603073Q0047657454696D6503043Q0006F82D2003053Q0016729D555403053Q00C7C41FCB4F03073Q00C8A4AB73A43D96026Q00F03F03093Q0074696D657374616D70026Q001040031B3Q00556E697444657461696C6564546872656174536974756174696F6E03063Q00AEF8025C86AC03053Q00E3DE94632503063Q00275340F1FC2703053Q0099532Q329603053Q00636F6C6F7203063Q005264721274AE03073Q002D3D16137C13CB030B3Q00426967576967734461746103083Q004D652Q736167657303063Q00D1071FE50E7503073Q00D9A1726D95621003043Q00102C2D7903063Q00147240581CDC027Q004002703Q001209010300014Q002Q010400043Q0026B5000300330001000100049E3Q003300012Q000F01055Q001209010600023Q001209010700034Q00790005000700020006FE0001002C0001000500049E3Q002C0001001209010500014Q002Q010600093Q0026B50005000C0001000100049E3Q000C00012Q00B3000A000E4Q006E0009000D6Q0008000C6Q0007000B6Q0006000A3Q00122Q000A00043Q00202Q000A000A00054Q000B00013Q00202Q000B000B00064Q000C3Q00034Q000D5Q00122Q000E00073Q00122Q000F00086Q000D000F000200122Q000E00096Q000E000100024Q000C000D000E4Q000D5Q00122Q000E000A3Q00122Q000F000B6Q000D000F00024Q000C000D00084Q000D5Q00122Q000E000C3Q00122Q000F000D6Q000D000F00024Q000C000D00094Q000A000C000100044Q002C000100049E3Q000C00012Q000F010500013Q00205A0005000500064Q000600013Q00202Q0006000600064Q000600066Q00040005000600122Q0003000E3Q0026B5000300020001000E00049E3Q0002000100066D0004006F00013Q00049E3Q006F000100122Q000500094Q006700050001000200203E00060004000F3Q000105000500060026F90005006F0001001000049E3Q006F0001001209010500014Q002Q010600073Q0026B50005003F0001000100049E3Q003F000100122Q000800114Q00DD00095Q00122Q000A00123Q00122Q000B00136Q0009000B00024Q000A5Q00122Q000B00143Q00122Q000C00156Q000A000C6Q00083Q00094Q000700096Q000600083Q00202Q0008000400164Q00095Q00122Q000A00173Q00122Q000B00186Q0009000B000200062Q000800580001000900049E3Q005800012Q000F010800023Q00203E0008000800190030890008001A000E00049E3Q006F000100203E0008000400162Q00B100095Q00122Q000A001B3Q00122Q000B001C6Q0009000B000200062Q000800660001000900049E3Q0066000100203E0008000400162Q00BF00095Q00122Q000A001D3Q00122Q000B001E6Q0009000B000200062Q0008006F0001000900049E3Q006F000100066D0006006F00013Q00049E3Q006F00012Q000F010800023Q00203E0008000800190030890008001A001F00049E3Q006F000100049E3Q003F000100049E3Q006F000100049E3Q000200012Q003F3Q00017Q000F3Q00028Q00026Q00F03F030F3Q005F5765616B41757261482Q6F6B6564030E3Q00682Q6F6B73656375726566756E63030D3Q00B4CD01A00C3EDD8AC526B0333403073Q00A8E4A160D95F512Q0103083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F6164656403093Q00BB3945E972179E3D5703063Q0062EC5C24823303083Q00A91C1FA944AFB02303083Q0050C4796CDA25C8D503063Q00137C17714F1D03073Q00EA6013621F2B6E003A3Q001209012Q00014Q003Q0100033Q0026B53Q001E0001000200049E3Q001E000100066D0001003900013Q00049E3Q0039000100066D0002003900013Q00049E3Q003900012Q000F01045Q00203E0004000400030006D7000400390001000100049E3Q00390001001209010400013Q000EF30001000D0001000400049E3Q000D000100122Q000500044Q000F010600013Q001209010700053Q001209010800064Q00790006000800020006E300073Q000100032Q00FD3Q00034Q000F012Q00014Q000F017Q00B00005000700012Q000F01055Q00308900050003000700049E3Q0039000100049E3Q000D000100049E3Q003900010026B53Q00020001000100049E3Q0002000100122Q000400083Q0020120004000400094Q000500013Q00122Q0006000A3Q00122Q0007000B6Q000500076Q00043Q00054Q000200056Q000100046Q00043Q00024Q000500013Q00122Q0006000C3Q00122Q0007000D6Q0005000700024Q00068Q0004000500064Q000500013Q00122Q0006000E3Q00122Q0007000F6Q0005000700024Q00068Q0004000500064Q000300043Q00124Q00023Q00044Q000200012Q003F3Q00013Q00013Q00373Q00028Q0003053Q007461626C6503063Q00696E7365727403063Q00736F756E647303093Q00CFD823593C43DADC3E03063Q0037BBB14E3C4F03073Q0047657454696D6503053Q003EC14AE54203073Q00E04DAE3F8B26AF026Q00F03F031B3Q00556E697444657461696C6564546872656174536974756174696F6E03063Q00944D5937815303043Q004EE4213803063Q00DA7FA00480DA03053Q00E5AE1ED26303093Q0074696D657374616D70026Q00104003053Q00736F756E6403093Q0020D7B267D07D1814C803073Q00597B8DE6318D5D030E3Q00C84BC23A2D0AC770E40B155EF67503063Q002A9311966C702Q033Q002EA90803063Q00886FC64D1F8703083Q003608B551B8F012AD03083Q00C96269C736DD8477030F3Q009B058461353CABAA56C3000E34BEB403073Q00CCD96CE3416255030B3Q00426967576967734461746103063Q00536F756E647303113Q007CCAF2A51BC959D0AFA51BC14CCDFCEB2B03063Q00A03EA395854C030F3Q00F4A90A6FF4DFA71E7583F7AC0C3DCE03053Q00A3B6C06D4F030B3Q000F1C34F6C8741201D5FB2003053Q0095544660A003053Q000C0718E32C03043Q008D58666D030F3Q009250C56509295CC2F374DF790E3C4703083Q00A1D333AA107A5D35027Q004003093Q00C094861EC6EE9327DE03043Q00489BCED22Q033Q0067757103053Q0053261A346E03083Q004D652Q736167657303083Q00632D13706557046503043Q002638774703023Q00D0CC03063Q0036938F38B645026Q000840030A3Q00EDBBCB7FE296AAF64AD403053Q00BFB6E19F2903044Q001B2B5E03073Q00A24B724835EBE701BD3Q001209010200014Q002Q010300053Q0026B50002001D0001000100049E3Q001D000100122Q000600023Q0020BB0006000600034Q00075Q00202Q0007000700044Q00083Q00024Q000900013Q00122Q000A00053Q00122Q000B00066Q0009000B000200122Q000A00076Q000A000100024Q00080009000A4Q000900013Q00122Q000A00083Q00122Q000B00096Q0009000B00024Q000800096Q0006000800014Q00065Q00202Q0006000600044Q00075Q00202Q0007000700044Q000700076Q00030006000700122Q0002000A3Q0026B5000200020001000A00049E3Q0002000100122Q0006000B4Q0090000700013Q00122Q0008000C3Q00122Q0009000D6Q0007000900024Q000800013Q00122Q0009000E3Q00122Q000A000F6Q0008000A6Q00063Q00074Q000500076Q000400063Q00062Q000300BC00013Q00049E3Q00BC000100122Q000600074Q006700060001000200203E0007000300103Q000106000600070026F9000600BC0001001100049E3Q00BC000100203E0006000300122Q00B1000700013Q00122Q000800133Q00122Q000900146Q00070009000200062Q000600560001000700049E3Q0056000100203E0006000300122Q00B1000700013Q00122Q000800153Q00122Q000900166Q00070009000200062Q000600560001000700049E3Q0056000100203E0006000300122Q00B1000700013Q00122Q000800173Q00122Q000900186Q00070009000200062Q000600560001000700049E3Q0056000100203E0006000300122Q00B1000700013Q00122Q000800193Q00122Q0009001A6Q00070009000200062Q000600560001000700049E3Q0056000100203E0006000300122Q00BF000700013Q00122Q0008001B3Q00122Q0009001C6Q00070009000200062Q0006005A0001000700049E3Q005A00012Q000F010600023Q00203E00060006001D0030890006001E000A00049E3Q00BC000100203E0006000300122Q00B1000700013Q00122Q0008001F3Q00122Q000900206Q00070009000200062Q000600810001000700049E3Q0081000100203E0006000300122Q00B1000700013Q00122Q000800213Q00122Q000900226Q00070009000200062Q000600810001000700049E3Q0081000100203E0006000300122Q00B1000700013Q00122Q000800233Q00122Q000900246Q00070009000200062Q000600810001000700049E3Q0081000100203E0006000300122Q00B1000700013Q00122Q000800253Q00122Q000900266Q00070009000200062Q000600810001000700049E3Q0081000100203E0006000300122Q00BF000700013Q00122Q000800273Q00122Q000900286Q00070009000200062Q000600850001000700049E3Q0085000100066D0004008100013Q00049E3Q008100010026F9000500850001000A00049E3Q008500012Q000F010600023Q00203E00060006001D0030890006001E002900049E3Q00BC000100203E0006000300122Q00B1000700013Q00122Q0008002A3Q00122Q0009002B6Q00070009000200062Q000600930001000700049E3Q0093000100203E0006000300122Q00BF000700013Q00122Q0008002C3Q00122Q0009002D6Q00070009000200062Q000600970001000700049E3Q009700012Q000F010600023Q00203E00060006001D0030890006002E000A00049E3Q00BC000100203E0006000300122Q00B1000700013Q00122Q0008002F3Q00122Q000900306Q00070009000200062Q000600A50001000700049E3Q00A5000100203E0006000300122Q00BF000700013Q00122Q000800313Q00122Q000900326Q00070009000200062Q000600A90001000700049E3Q00A900012Q000F010600023Q00203E00060006001D0030890006001E003300049E3Q00BC000100203E0006000300122Q00B1000700013Q00122Q000800343Q00122Q000900356Q00070009000200062Q000600B70001000700049E3Q00B7000100203E0006000300122Q00BF000700013Q00122Q000800363Q00122Q000900376Q00070009000200062Q000600BC0001000700049E3Q00BC00012Q000F010600023Q00203E00060006001D0030890006001E001100049E3Q00BC000100049E3Q000200012Q003F3Q00017Q000C3Q00028Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q002E1A40C89E7D9F070B5BC8A203073Q00EB667F32A7CC12030C3Q004865726F526F746174696F6E03123Q005F4D794C6567656E64617279482Q6F6B6564030E3Q00682Q6F6B73656375726566756E6303093Q004E616D65706C61746503073Q0071A5F10A47215E03063Q004E30C19543242Q0100293Q001209012Q00014Q003Q0100023Q000EF30001000200013Q00049E3Q0002000100122Q000300023Q0020100103000300034Q00045Q00122Q000500043Q00122Q000600056Q000400066Q00033Q00044Q000200046Q000100033Q00062Q0001002800013Q00049E3Q0028000100066D0002002800013Q00049E3Q0028000100122Q000300064Q000F010400013Q00203E0004000400070006D7000400280001000100049E3Q00280001001209010400013Q0026B5000400170001000100049E3Q0017000100122Q000500083Q0020820006000300094Q00075Q00122Q0008000A3Q00122Q0009000B6Q0007000900020006E300083Q000100012Q000F012Q00014Q00B00005000800012Q000F010500013Q00308900050007000C00049E3Q0028000100049E3Q0017000100049E3Q0028000100049E3Q000200012Q003F3Q00013Q00013Q00063Q0003063Q00556E6974494403063Q0048724461746103053Q00546F6B656E03063Q00737472696E6703053Q006C6F7765720002113Q00066D3Q000D00013Q00049E3Q000D000100203E00023Q000100066D0002000D00013Q00049E3Q000D00012Q000F01025Q00204500020002000200122Q000300043Q00202Q00030003000500202Q00043Q00014Q00030002000200102Q00020003000300044Q001000012Q000F01025Q00203E0002000200020030890002000300062Q003F3Q00017Q000B3Q00028Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q00181B9217733F0A810C483F1003053Q0021507EE078030C3Q004865726F526F746174696F6E030B3Q005F54657874482Q6F6B6564030E3Q00682Q6F6B73656375726566756E63030D3Q00CFA910D07DE2A60CD05DF8AD0703053Q003C8CC863A42Q0100293Q001209012Q00014Q003Q0100023Q0026B53Q00020001000100049E3Q0002000100122Q000300023Q0020100103000300034Q00045Q00122Q000500043Q00122Q000600056Q000400066Q00033Q00044Q000200046Q000100033Q00062Q0001002800013Q00049E3Q0028000100066D0002002800013Q00049E3Q0028000100122Q000300064Q000F010400013Q00203E0004000400070006D7000400280001000100049E3Q00280001001209010400013Q0026B5000400170001000100049E3Q0017000100122Q000500084Q001E000600036Q00075Q00122Q000800093Q00122Q0009000A6Q0007000900020006E300083Q000100012Q000F012Q00014Q00B00005000800012Q000F010500013Q00308900050007000B00049E3Q0028000100049E3Q0017000100049E3Q0028000100049E3Q000200012Q003F3Q00013Q00013Q00023Q0003063Q0048724461746103083Q00436173745465787405044Q000F01055Q00203E0005000500010010A70005000200022Q003F3Q00017Q00053Q00028Q00026Q00F03F030A3Q00556E6974457869737473030A3Q00556E69744865616C7468030D3Q00556E69744865616C74684D617801273Q0012092Q0100014Q002Q010200023Q0026B5000100060001000200049E3Q00060001001209010300014Q007E000300023Q0026B5000100020001000100049E3Q0002000100122Q000300034Q00FD00046Q00F00003000200022Q00FD000200033Q00066D0002002400013Q00049E3Q00240001001209010300014Q002Q010400053Q0026B50003001F0001000100049E3Q001F000100122Q000600044Q00FD00076Q00F00006000200020006DE000400180001000600049E3Q00180001001209010400013Q00122Q000600054Q00FD00076Q00F00006000200020006DE0005001E0001000600049E3Q001E0001001209010500023Q001209010300023Q0026B5000300100001000200049E3Q001000012Q001B0106000400052Q007E000600023Q00049E3Q001000010012092Q0100023Q00049E3Q000200012Q003F3Q00017Q000C3Q00024Q00E4DF1A41028Q0003073Q0047657454696D65030B3Q00556E6974496E52616E676503063Q00560FE835560403063Q00762663894C3303053Q007461626C6503063Q00696E7365727403043Q00E8280C0603063Q00409D4665726903063Q0048ADA6EF044803053Q007020C8C7830A4A4Q000F010B6Q0038000B000B00090006D7000B00120001000100049E3Q0012000100066D0003001200013Q00049E3Q001200012Q000F010B00013Q0006B6000300140001000B00049E3Q001400012Q000F010B00023Q0006B6000300140001000B00049E3Q001400012Q000F010B00033Q0006B6000300140001000B00049E3Q001400012Q000F010B00043Q0006B6000300140001000B00049E3Q001400010026B5000900490001000100049E3Q00490001001209010B00024Q002Q010C000C3Q0026B5000B00160001000200049E3Q0016000100122Q000D00034Q00ED000D000100024Q000C0005000D4Q000D00056Q000D0004000D00062Q000C00490001000D00049E3Q00490001001209010D00024Q002Q010E000E3Q0026B5000D00210001000200049E3Q002100012Q000F010F00064Q000F011000074Q00F0000F000200022Q00FD000E000F3Q000E0C010200490001000E00049E3Q0049000100122Q000F00044Q000F011000074Q00F0000F000200020006D7000F00350001000100049E3Q003500012Q000F010F00074Q00BF001000083Q00122Q001100053Q00122Q001200066Q00100012000200062Q000F00490001001000049E3Q0049000100122Q000F00073Q0020DB000F000F00084Q001000096Q00113Q00024Q001200083Q00122Q001300093Q00122Q0014000A6Q0012001400024Q001300076Q0011001200134Q001200083Q00122Q0013000B3Q00122Q0014000C6Q0012001400024Q00110012000E4Q000F0011000100044Q0049000100049E3Q0021000100049E3Q0049000100049E3Q001600012Q003F3Q00017Q00013Q0003063Q006865616C746802083Q00203E00023Q000100203E000300010001000641000200050001000300049E3Q000500012Q00C300026Q0005010200014Q007E000200024Q003F3Q00017Q000C3Q00028Q0003083Q00556E69744E616D6500030C3Q00556E69744973467269656E6403063Q00945BFF43814503043Q003AE4379E2Q0103083Q00417572615574696C030B3Q00466F724561636841757261030C3Q009CA8E2031A9819A8BBF1071803073Q0055D4E9B04E5CCD026Q00F03F02363Q001209010200014Q002Q010300033Q0026B5000200300001000100049E3Q0030000100122Q000400024Q00FD00056Q00F00004000200022Q00FD000300043Q00261D0003002F0001000300049E3Q002F00012Q000F01046Q00380004000400030006D70004002F0001000100049E3Q002F0001001209010400014Q002Q010500053Q000EF3000100100001000400049E3Q0010000100122Q000600044Q00BE000700013Q00122Q000800053Q00122Q000900066Q0007000900024Q00088Q0006000800024Q000500063Q00262Q0005002F0001000300049E3Q002F00010026B50005002F0001000700049E3Q002F000100122Q000600083Q00201A0006000600094Q00078Q000800013Q00122Q0009000A3Q00122Q000A000B6Q0008000A00024Q000900093Q0006E3000A3Q000100052Q000F012Q00024Q000F012Q00034Q000F012Q00044Q000F012Q00054Q00FD3Q00014Q00B00006000A000100049E3Q002F000100049E3Q001000010012090102000C3Q0026B5000200020001000C00049E3Q00020001001209010400014Q007E000400023Q00049E3Q000200012Q003F3Q00013Q00017Q000A113Q00066D0003001000013Q00049E3Q001000012Q000F010B5Q0006B60003000E0001000B00049E3Q000E00012Q000F010B00013Q0006B60003000E0001000B00049E3Q000E00012Q000F010B00023Q0006B60003000E0001000B00049E3Q000E00012Q000F010B00033Q0006FE000300100001000B00049E3Q001000012Q000F010B00044Q007E000B00024Q003F3Q00017Q005E3Q0003153Q00906F24D785713ACB8E7720DC896D22D1976C37C28403043Q008EC0236503173Q00FA5A0887CEA28B29E5561B86C2A29332FF460881CBA98803083Q0076B61549C387ECCC028Q0003023Q005F4703143Q006E616D65706C6174654C556E697473436163686503093Q00556E6974436C612Q7303063Q0018301B59011F03073Q009D685C7A20646D026Q00F03F03113Q004765745370656369616C697A6174696F6E03153Q004765745370656369616C697A6174696F6E496E666F027Q0040026Q001040030D3Q004973506C617965725370652Q6C025Q00B07D4003053Q0080B3DDD93803083Q00CBC3C6AFAA5D47ED025Q00EDF54003053Q00034A39DC5203073Q009C4E2B5EB53171026Q000840024Q00DC051641024Q004450164103063Q0042E7CDB0044D03073Q00191288A4C36B23024Q002019094103053Q00C52CAE467103083Q00D8884DC92F12DCA1025Q00F5094103063Q001DE322C907D203073Q00E24D8C4BBA68BC03073Q009DC7C33A4EAACB03053Q002FD9AEB05F024Q00A0A10A41024Q0060140A4103073Q009CD46507B3477D03083Q0046D8BD1662D2341803063Q00EAD0AA94DCD403053Q00B3BABFC3E7024Q00A0601741024Q00C055E94003053Q00DA2A0AF7FC03043Q0084995F78024Q00A0D71741024Q0010140A4103073Q0095BB1D28F6C9A503073Q00C0D1D26E4D97BA024Q00E8F2174103053Q00C316302QFA03063Q00A4806342899F03063Q003086E0AD0F8703043Q00DE60E989025Q00BCA54003053Q009AA6B50C8D03073Q0090D9D3C77FE893024Q0028BC1741025Q00FD174103063Q00C820373BDA4B03083Q0024984F5E48B5256203073Q00F3D1543AD6CB4203043Q005FB7B82703063Q00737472696E6703053Q00752Q70657203013Q003A03113Q00910DD20F70DA30900CD30966A1369C10C903073Q0062D55F874634E003123Q00CD8BE85A75D0F9FB5267CA8CFB5660D78CE703053Q00349EC3A917030B3Q004A8E1B51B50121A355900B03083Q00EB1ADC5214E6551B03113Q00B893C0E747BCFBCDEB47AB88D9EE5DA68403053Q0014E8C189A2030F3Q000FF0EB8DBDA13E4216E8E087D1A92503083Q001142BFA5C687EC7703133Q002A9981382QDAB6E13D8A9D36CDDECDE5262Q8003083Q00B16FCFCE739F888C030C3Q0035A83C35F066715FA13F38ED03073Q003F65E97074B42F03053Q00EE3AEA1BFB03063Q0056A35B8D729803043Q007D245A5603053Q005A336B141303063Q00A5D5A4C318BF03053Q005DED90E58F03053Q00382QF7100803063Q0026759690796B03153Q00039AC31F128BC21B199ED10F0392DA050C9FCA1F0903043Q005A4DDB8E031F3Q0048616E646C654C4E616D65706C617465556E6974734361636865412Q64656403173Q00C8250C1C733756C7300406792953D23B131C61284CC32003073Q001A866441592C6703213Q0048616E646C654C4E616D65706C617465556E697473436163686552656D6F7665640343013Q00B100045Q00122Q000500013Q00122Q000600026Q00040006000200062Q0001000C0001000400049E3Q000C00012Q000F01045Q001209010500033Q001209010600044Q00790004000600020006FE0001002B2Q01000400049E3Q002B2Q01001209010400054Q002Q0105000E3Q0026B50004001D0001000500049E3Q001D000100122Q000F00064Q001500105Q00102Q000F0007001000122Q000F00086Q00105Q00122Q001100093Q00122Q0012000A6Q001000126Q000F3Q00114Q000700116Q000600106Q0005000F3Q00122Q0004000B3Q000EF3000B002C0001000400049E3Q002C000100122Q000F000C4Q0076000F000100024Q0008000F3Q00122Q000F000D6Q001000086Q000F000200144Q000E00146Q000D00136Q000C00126Q000B00116Q000A00106Q0009000F3Q00122Q0004000E3Q0026B50004000E0001000E00049E3Q000E000100066D000A00422Q013Q00049E3Q00422Q0100066D000600422Q013Q00049E3Q00422Q01001209010F00054Q002Q011000103Q0026B5000F004B0001000F00049E3Q004B000100122Q001100103Q001209011200114Q00F000110002000200066D0011004000013Q00049E3Q004000012Q000F01115Q001209011200123Q001209011300134Q00790011001300022Q00C9001100013Q00122Q001100103Q001209011200144Q00F000110002000200066D001100422Q013Q00049E3Q00422Q012Q000F01115Q001292001200153Q00122Q001300166Q0011001300024Q001100023Q00044Q00422Q010026B5000F00760001001700049E3Q0076000100122Q001100103Q001209011200184Q00F00011000200020006D7001100570001000100049E3Q0057000100122Q001100103Q001209011200194Q00F000110002000200066D0011005C00013Q00049E3Q005C00012Q000F01115Q0012090112001A3Q0012090113001B4Q00790011001300022Q00C9001100033Q00122Q001100103Q0012090112001C4Q00F000110002000200066D0011006600013Q00049E3Q006600012Q000F01115Q0012090112001D3Q0012090113001E4Q00790011001300022Q00C9001100023Q00122Q001100103Q0012090112001F4Q00F000110002000200066D0011007500013Q00049E3Q007500012Q000F01115Q0012C5001200203Q00122Q001300216Q0011001300024Q00125Q00122Q001300223Q00122Q001400236Q0012001400024Q001200046Q001100033Q001209010F000F3Q000EF3000E00AB0001000F00049E3Q00AB000100122Q001100103Q001209011200244Q00F00011000200020006D7001100820001000100049E3Q0082000100122Q001100103Q001209011200254Q00F000110002000200066D0011008C00013Q00049E3Q008C00012Q000F01115Q0012C5001200263Q00122Q001300276Q0011001300024Q00125Q00122Q001300283Q00122Q001400296Q0012001400024Q001200036Q001100043Q00122Q001100103Q0012090112002A4Q00F00011000200020006D7001100960001000100049E3Q0096000100122Q001100103Q0012090112002B4Q00F000110002000200066D0011009B00013Q00049E3Q009B00012Q000F01115Q0012090112002C3Q0012090113002D4Q00790011001300022Q00C9001100013Q00122Q001100103Q0012090112002E4Q00F00011000200020006D7001100A50001000100049E3Q00A5000100122Q001100103Q0012090112002F4Q00F000110002000200066D001100AA00013Q00049E3Q00AA00012Q000F01115Q001209011200303Q001209011300314Q00790011001300022Q00C9001100043Q001209010F00173Q0026B5000F00DB0001000B00049E3Q00DB000100122Q001100103Q001209011200324Q00F000110002000200066D001100BC00013Q00049E3Q00BC00012Q000F01115Q0012C5001200333Q00122Q001300346Q0011001300024Q00125Q00122Q001300353Q00122Q001400366Q0012001400024Q001200036Q001100013Q00122Q001100103Q001209011200374Q00F000110002000200066D001100C600013Q00049E3Q00C600012Q000F01115Q001209011200383Q001209011300394Q00790011001300022Q00C9001100013Q00122Q001100103Q0012090112003A4Q00F00011000200020006D7001100D00001000100049E3Q00D0000100122Q001100103Q0012090112003B4Q00F000110002000200066D001100DA00013Q00049E3Q00DA00012Q000F01115Q0012C50012003C3Q00122Q0013003D6Q0011001300024Q00125Q00122Q0013003E3Q00122Q0014003F6Q0012001400024Q001200046Q001100033Q001209010F000E3Q000EF3000500340001000F00049E3Q0034000100122Q001100403Q00206C0011001100414Q001200063Q00122Q001300426Q0014000A6Q0012001200144Q0011000200024Q001000116Q00115Q00122Q001200433Q00122Q001300446Q00110013000200062Q0010000F2Q01001100049E3Q000F2Q012Q000F01115Q001209011200453Q001209011300464Q00790011001300020006B60010000F2Q01001100049E3Q000F2Q012Q000F01115Q001209011200473Q001209011300484Q00790011001300020006B60010000F2Q01001100049E3Q000F2Q012Q000F01115Q001209011200493Q0012090113004A4Q00790011001300020006B60010000F2Q01001100049E3Q000F2Q012Q000F01115Q0012090112004B3Q0012090113004C4Q00790011001300020006B60010000F2Q01001100049E3Q000F2Q012Q000F01115Q0012090112004D3Q0012090113004E4Q00790011001300020006B60010000F2Q01001100049E3Q000F2Q012Q000F01115Q0012090112004F3Q001209011300504Q00790011001300020006FE001000142Q01001100049E3Q00142Q012Q000F01115Q001209011200513Q001209011300524Q00790011001300022Q00C9001100024Q000F011100024Q00BF00125Q00122Q001300533Q00122Q001400546Q00120014000200062Q001100262Q01001200049E3Q00262Q012Q000F01115Q001209011200553Q001209011300564Q00790011001300020006FE000E00262Q01001100049E3Q00262Q012Q000F01115Q001209011200573Q001209011300584Q00790011001300022Q00C9001100023Q001209010F000B3Q00049E3Q0034000100049E3Q00422Q0100049E3Q000E000100049E3Q00422Q012Q000F01045Q001209010500593Q0012090106005A4Q00790004000600020006FE000100372Q01000400049E3Q00372Q0100066D000200422Q013Q00049E3Q00422Q0100122Q0004005B4Q00FD000500024Q007700040002000100049E3Q00422Q012Q000F01045Q0012090105005C3Q0012090106005D4Q00790004000600020006FE000100422Q01000400049E3Q00422Q0100066D000200422Q013Q00049E3Q00422Q0100122Q0004005E4Q00FD000500024Q00770004000200012Q003F3Q00017Q00183Q00028Q00030B3Q00435F4E616D65506C61746503133Q004765744E616D65506C617465466F72556E697403123Q006E616D65506C617465556E6974546F6B656E03083Q00556E69744E616D65026Q00F03F027Q0040030A3Q00D6E23D268BF3E93520B003053Q00C49183504303073Q0028B50E011BE41B03063Q00887ED066687803023Q005F4703143Q006E616D65706C6174654C556E697473436163686503093Q006D84C7579F5E3C457D03083Q003118EAAE23CF325D03083Q0019FCF49C5F0DFFF803053Q00116C929DE803083Q005ECD1DF9089D62E703063Q00C82BA3748D4F03063Q00AA38349799F003073Q0083DF565DE3D09403083Q00556E69744755494403083Q0073747273706C697403013Q002D01533Q0012092Q0100014Q002Q010200023Q0026B5000100020001000100049E3Q0002000100122Q000300023Q0020F80003000300034Q00048Q000500016Q0003000500024Q000200033Q00062Q0002005200013Q00049E3Q00520001001209010300014Q002Q010400093Q0026B5000300160001000100049E3Q0016000100203E000400020004001246000A00056Q000B00046Q000A000200024Q0005000A3Q00122Q000300063Q0026B50003003D0001000700049E3Q003D00012Q000F010A5Q001209010B00083Q001209010C00094Q0079000A000C00020006FE000700240001000A00049E3Q002400012Q000F010A5Q001209010B000A3Q001209010C000B4Q0079000A000C00020006B6000700520001000A00049E3Q0052000100122Q000A000C3Q002003000A000A000D4Q000B3Q00044Q000C5Q00122Q000D000E3Q00122Q000E000F6Q000C000E00024Q000B000C00044Q000C5Q00122Q000D00103Q00122Q000E00116Q000C000E00024Q000B000C00054Q000C5Q00122Q000D00123Q00122Q000E00136Q000C000E00024Q000B000C00064Q000C5Q00122Q000D00143Q00122Q000E00156Q000C000E00024Q000B000C00094Q000A0004000B00044Q005200010026B50003000E0001000600049E3Q000E000100122Q000A00164Q000B000B00046Q000A000200024Q0006000A3Q00122Q000A00173Q00122Q000B00186Q000C00066Q000A000C00104Q000800106Q0009000F6Q0008000E6Q0008000D6Q0008000C6Q0008000B6Q0007000A3Q00122Q000300073Q00044Q000E000100049E3Q0052000100049E3Q000200012Q003F3Q00017Q00033Q0003023Q005F4703143Q006E616D65706C6174654C556E69747343616368650001093Q00122Q000100013Q00203E0001000100022Q0038000100013Q00261D000100080001000300049E3Q0008000100122Q000100013Q00203E0001000100020020D200013Q00032Q003F3Q00017Q00273Q00028Q00026Q00F03F03053Q00706169727303063Q00435F4974656D030D3Q0049734974656D496E52616E6765027Q0040026Q001040026Q00084003073Q00435F5370652Q6C030C3Q004765745370652Q6C496E666F025Q00C0524003043Q006E616D6500030E3Q0049735370652Q6C496E52616E676503053Q007370652Q6C03043Q005A078AB303073Q00E43466E7D6C5D003043Q000CE17BC103083Q00B67E8015AA8AEB7903043Q0082D93AE803083Q0066EBBA5586E6735003083Q00540D2D4B46DD2F5203073Q0042376C5E3F12B403083Q0019848B052657138803063Q003974EDE5574703083Q00A7B0F5D576E040AF03073Q0027CAD18D87178E03073Q00EC230C063ED1DB03063Q00989F53696A52030C3Q008ED458F5C05280CA78F1C65203063Q003CE1A63192A9026Q0020402Q01026Q005940030C3Q00556E69745265616374696F6E03063Q003F122E33041503063Q00674F7E4F4A6103063Q00AA73D26A5B0803063Q007ADA1FB3133E01A43Q0012092Q0100014Q002Q010200053Q0026B5000100160001000200049E3Q0016000100122Q000600034Q000F01076Q002500060002000800049E3Q0012000100122Q000B00043Q0020E0000B000B00054Q000C00096Q000D8Q000B000D000200062Q000B001200013Q00049E3Q00120001000669000A00120001000200049E3Q001200012Q00FD0002000A3Q000663000600080001000200049E3Q000800012Q002Q010300033Q0012092Q0100063Q0026B5000100190001000700049E3Q001900012Q007E000200023Q0026B5000100850001000800049E3Q0085000100066D0005003400013Q00049E3Q00340001001209010600013Q0026B50006001E0001000100049E3Q001E000100122Q000700093Q0020F200070007000A00122Q0008000B6Q0007000200024Q000300073Q00202Q00070003000C00262Q0007002F0001000D00049E3Q002F000100122Q000700093Q00207B00070007000E00202Q00080003000C4Q00098Q0007000900024Q000400073Q00044Q007F00012Q00C300046Q0005010400013Q00049E3Q007F000100049E3Q001E000100049E3Q007F0001001209010600014Q002Q0107000E3Q0026B50006006E0001000100049E3Q006E000100122Q000F000A3Q0012D60010000F6Q000F000200164Q000E00166Q000D00156Q000C00146Q000B00136Q000A00126Q000900116Q000800106Q0007000F6Q000F3Q00084Q001000013Q00122Q001100103Q00122Q001200116Q0010001200024Q000F001000074Q001000013Q00122Q001100123Q00122Q001200136Q0010001200024Q000F001000084Q001000013Q00122Q001100143Q00122Q001200156Q0010001200024Q000F001000094Q001000013Q00122Q001100163Q00122Q001200176Q0010001200024Q000F0010000A4Q001000013Q00122Q001100183Q00122Q001200196Q0010001200024Q000F0010000B4Q001000013Q00122Q0011001A3Q00122Q0012001B6Q0010001200024Q000F0010000C4Q001000013Q00122Q0011001C3Q00122Q0012001D6Q0010001200024Q000F0010000D4Q001000013Q00122Q0011001E3Q00122Q0012001F6Q0010001200024Q000F0010000E4Q0003000F3Q00122Q000600023Q0026B5000600360001000200049E3Q0036000100203E000F0003000C00261D000F007C0001000D00049E3Q007C000100122Q000F000E3Q00203E00100003000C2Q00FD00116Q0079000F001100020026B5000F007C0001000200049E3Q007C00012Q0005010F00013Q0006DE0004007D0001000F00049E3Q007D00012Q000501045Q00049E3Q007F000100049E3Q0036000100260E010200840001002000049E3Q008400010026B5000400840001002100049E3Q00840001001209010200203Q0012092Q0100073Q0026B50001009D0001000100049E3Q009D0001001209010200223Q0012E7000600236Q000700013Q00122Q000800243Q00122Q000900256Q0007000900022Q00FD00086Q007900060008000200066D0006009B00013Q00049E3Q009B000100122Q000600234Q0058000700013Q00122Q000800263Q00122Q000900276Q0007000900024Q00088Q00060008000200262Q0006009B0001000700049E3Q009B000100049E3Q009C00012Q007E000200023Q0012092Q0100023Q0026B5000100020001000600049E3Q000200012Q002Q010400044Q0005010500013Q0012092Q0100083Q00049E3Q000200012Q003F3Q00017Q00393Q00031B3Q00F25AD3CC75F444DFD466E455C9CC75E45CDBD664E258C5CB7EE84403053Q002AA7149A9803133Q007FD08B764E127ADB8E6E520079CA9D71450E7A03063Q00412A9EC22211031B3Q002F097B3812DE2BCB360B712D1ED924CB37177D3B08DF24DD2E086203083Q008E7A47326C4D8D7B031A3Q00208CD62C042692DA34173683CC2C043C8CCB3D092797CF2C1E3103053Q005B75C29F7803183Q002F33172C0AC2143F31123B14C210252E0B3B16D4013E381A03073Q00447A7D5E78559103023Q005F4703143Q00496E74652Q727570744C556E69747343616368650003063Q00737472696E6703053Q006D6174636803093Q00191DC25BD8D5BB031903073Q00DA777CAF3EA8B9028Q00031C3Q0090DE61F09AC378E189DC6BE596C477E78DD166EA80DC77F791D17AF003043Q00A4C59028031D3Q00B6DE83BFE285B3D586A7FE97B0C495A8F597ADDE8FA7E283B3D48BBFF803063Q00D6E390CAEBBD031C3Q00D88BAE4F2F806319C189A45A23876C19C095A84C35816C0FD984B54F03083Q005C8DC5E71B70D333031D3Q00D3D1A397EED5CFAF8FFDC5DEB997EEC3D2BA8CE6C3CDB596E1C2DEBE8603053Q00B1869FEAC303073Q009EC31E8EE798C703053Q00A9DD8B5FC003143Q00EBA5560B1D15EEAE53130107EDBF400C1607ECBF03063Q0046BEEB1F5F4203043Q0099C329D203053Q0085DA827A86026Q00F03F030C3Q004B69636B5370652Q6C49647303073Q001FD7C2EAF2861403073Q00585C9F83A4BCC3030F3Q00556E69744368612Q6E656C496E666F0100030C3Q00556E69745265616374696F6E03063Q009022BE52D2F903073Q00BDE04EDF2BB78B03063Q003EF08B0FC43C03053Q00A14E9CEA76026Q00104003043Q008496FAE803043Q00BCC7D7A9030F3Q00556E697443617374696E67496E666F03063Q00EC055E62EDEE03053Q00889C693F1B03063Q000B80782D1E9E03043Q00547BEC1903073Q00E39BAF1BA09CF403063Q00D590EBCA77CC03063Q003719CC2Q2D3703073Q002D4378BE4A4843030D3Q00292CF9A0EB9AFBF93416F4B5FC03083Q008940428DC599E88E06E54Q00B100075Q00122Q000800013Q00122Q000900026Q00070009000200062Q0001001E0001000700049E3Q001E00012Q000F01075Q001209010800033Q001209010900044Q00790007000900020006B60001001E0001000700049E3Q001E00012Q000F01075Q001209010800053Q001209010900064Q00790007000900020006B60001001E0001000700049E3Q001E00012Q000F01075Q001209010800073Q001209010900084Q00790007000900020006B60001001E0001000700049E3Q001E00012Q000F01075Q001209010800093Q0012090109000A4Q00790007000900020006FE000100220001000700049E3Q0022000100122Q0007000B3Q00203E00070007000C0020D200070002000D00049E3Q00E4000100122Q0007000E3Q0020B700070007000F4Q000800026Q00095Q00122Q000A00103Q00122Q000B00116Q0009000B6Q00073Q000200062Q000700E400013Q00049E3Q00E40001001209010700124Q002Q010800093Q0026B50007005B0001001200049E3Q005B00012Q002Q010800084Q00B1000A5Q00122Q000B00133Q00122Q000C00146Q000A000C000200062Q000100490001000A00049E3Q004900012Q000F010A5Q001209010B00153Q001209010C00164Q0079000A000C00020006B6000100490001000A00049E3Q004900012Q000F010A5Q001209010B00173Q001209010C00184Q0079000A000C00020006B6000100490001000A00049E3Q004900012Q000F010A5Q001209010B00193Q001209010C001A4Q0079000A000C00020006FE0001004F0001000A00049E3Q004F00012Q000F010A5Q001204010B001B3Q00122Q000C001C6Q000A000C00024Q0008000A3Q00044Q005A00012Q000F010A5Q001209010B001D3Q001209010C001E4Q0079000A000C00020006FE0001005A0001000A00049E3Q005A00012Q000F010A5Q001209010B001F3Q001209010C00204Q0079000A000C00022Q00FD0008000A3Q001209010700213Q000EF30021002E0001000700049E3Q002E000100122Q000A000B3Q00203E000A000A00222Q0038000A000A00040006DE000900630001000A00049E3Q006300012Q000F010900013Q00066D000900E400013Q00049E3Q00E40001001209010A00124Q002Q010B000B3Q000EF3001200C90001000A00049E3Q00C900012Q0005010B6Q00BF000C5Q00122Q000D00233Q00122Q000E00246Q000C000E000200062Q0008009A0001000C00049E3Q009A0001001209010C00124Q002Q010D00163Q0026B5000C00720001001200049E3Q0072000100122Q001700254Q004F001800026Q0017000200204Q001600206Q0015001F6Q0014001E6Q0013001D6Q0012001C6Q0011001B6Q0010001A6Q000F00196Q000E00186Q000D00173Q00262Q001300950001002600049E3Q0095000100122Q001700274Q008E00185Q00122Q001900283Q00122Q001A00296Q0018001A00024Q001900026Q00170019000200062Q000B00970001001700049E3Q0097000100122Q001700274Q009300185Q00122Q0019002A3Q00122Q001A002B6Q0018001A00024Q001900026Q00170019000200262Q001700960001002C00049E3Q009600012Q00C3000B6Q0005010B00013Q00049E3Q00C8000100049E3Q0072000100049E3Q00C800012Q000F010C5Q001209010D002D3Q001209010E002E4Q0079000C000E00020006FE000800C80001000C00049E3Q00C80001001209010C00124Q002Q010D00153Q0026B5000C00A20001001200049E3Q00A2000100122Q0016002F4Q0021001700026Q00160002001E4Q0015001E6Q0014001D6Q0013001C6Q0012001B6Q0011001A6Q001000196Q000F00186Q000E00176Q000D00163Q00262Q001400C40001002600049E3Q00C4000100122Q001600274Q008E00175Q00122Q001800303Q00122Q001900316Q0017001900024Q001800026Q00160018000200062Q000B00C60001001600049E3Q00C6000100122Q001600274Q009300175Q00122Q001800323Q00122Q001900336Q0017001900024Q001800026Q00160018000200262Q001600C50001002C00049E3Q00C500012Q00C3000B6Q0005010B00013Q00049E3Q00C8000100049E3Q00A20001001209010A00213Q0026B5000A00670001002100049E3Q0067000100066D000B00E400013Q00049E3Q00E4000100122Q000C000B3Q0020E5000C000C000C4Q000D3Q00034Q000E5Q00122Q000F00343Q00122Q001000356Q000E001000024Q000D000E00044Q000E5Q00122Q000F00363Q00122Q001000376Q000E001000024Q000D000E00024Q000E5Q00122Q000F00383Q00122Q001000396Q000E001000024Q000D000E00084Q000C0002000D00044Q00E4000100049E3Q0067000100049E3Q00E4000100049E3Q002E00012Q003F3Q00017Q00893Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q0075E956856FE3508B49E54B8403043Q00EA3D8C24030C3Q004865726F526F746174696F6E03073Q004865726F4C696203043Q00556E697403063Q00506C6179657203163Q00476574456E656D696573496E4D656C2Q6552616E6765026Q00244003113Q00476574456E656D696573496E52616E6765026Q00444003063Q0054617267657403173Q00476574456E656D696573496E53706C61736852616E6765028Q0003063Q00487244617461030D3Q00546172676574496E4D656C2Q65030D3Q00546172676574496E52616E6765030E3Q00546172676574496E53706C617368030D3Q004C65667449636F6E4672616D6503093Q00497356697369626C65026Q00F03F030B3Q00435F4E616D65506C61746503133Q004765744E616D65506C617465466F72556E697403113Q006E616D65506C617465556E69744755494403083Q00556E69744755494403093Q002CD2AF610A2ECBBF6003053Q006F41BDDA1203073Q004379636C654D4F2Q0103093Q004379636C65556E69740100030C3Q004379636C655370652Q6C494403023Q00494403053Q00546F6B656E030D3Q004D61696E49636F6E4672616D65030A3Q004E6F74496E52616E676503073Q005370652Q6C494403073Q0054657874757265030E3Q00476574566572746578436F6C6F72029A5Q99D93F03023Q005F47030D3Q004C48656B696C6952656349644C03133Q004C4865726F526F746174696F6E52656349644C030C3Q004C436F6E524F52656349644C030D3Q004C4D617844505352656349644C03073Q00435F5370652Q6C03103Q004765745370652Q6C432Q6F6C646F776E025Q00EFED4003093Q00737461727454696D6503083Q006475726174696F6E03083Q00746F6E756D62657203073Q004765744356617203103Q00705B1E39076DBA465E1E2Q0252AB4C5C03073Q00CF232B7B556B3C030B3Q004765744E65745374617473030F3Q00556E697443617374696E67496E666F03063Q0060A6A1F37C6203053Q001910CAC08A030F3Q00556E69744368612Q6E656C496E666F03063Q00EDC7ACFBACE603063Q00949DABCD82C903063Q000BD17F20DDFF03063Q009643B41449B103083Q0048656B696C69444203083Q0070726F66696C657303073Q0044656661756C7403073Q00746F2Q676C657303043Q006D6F646503053Q0076616C7565034Q0003083Q009F1D1B4E99110C4803043Q002DED787A03043Q00D3FDA32003043Q004CB788C2025Q0097F34003073Q005072696D6172792Q033Q00414F45027Q004003053Q002Q7F27D48A03083Q00583C104986C5757C03063Q007DEBE0EC716303053Q0021308A98A8030A3Q00476C6F62616C44617461030E3Q00526F746174696F6E48656C70657203113Q004C6567656E6461727953652Q74696E677303083Q0053652Q74696E6773030E3Q0060192450D53E7D2Q1854CD27770403063Q005712765031A103063Q00641BD1A9BC4503053Q00D02C7EBAC003053Q004379636C6503143Q0048656B696C69446973706C61795072696D617279030F3Q005265636F2Q6D656E646174696F6E7303093Q00696E64696361746F720003053Q00F403A7CA1103083Q002E977AC4A6749CA9030E3Q00456E656D696573496E4D656C2Q6503043Q006D6174682Q033Q006D6178030C3Q004C52616E6765436865636B4C030C3Q00556E697473496E4D656C2Q6503063Q0048656B696C6903053Q005374617465030E3Q006163746976655F656E656D696573030E3Q00456E656D696573496E52616E6765030C3Q00556E697473496E52616E6765030E3Q00432Q6F6C646F776E546F2Q676C6503063Q00746F2Q676C6503093Q00632Q6F6C646F776E73030C3Q00466967687452656D61696E73030B3Q006C6F6E676573745F2Q7464030C3Q00CDE85415C9EAF9470EF2EAE303053Q009B858D267A03123Q004865726F526F746174696F6E43686172444203073Q00546F2Q676C6573030C3Q004D617854696D65546F44696503053Q000625A2736003073Q00C5454ACC212F1F026Q00084003053Q00436F6E524F03073Q005461726765747303053Q00DD4A5682F503043Q00E7902F3A03023Q00E68803083Q0059D2B8BA15785DAF03113Q00436F6E524F5F427572737442752Q746F6E03103Q00436F6E524F5F46752Q6C42752Q746F6E030C3Q0047657454696D65546F44696503063Q009C5264F1490903063Q005AD1331CB51903063Q004D617844707303083Q00536D617274416F65030D3Q0052616E6765546F54617267657403063Q00C47A45E9BAC403053Q00DFB01B378E0291033Q007C00028Q0002000100014Q000200016Q0002000100014Q000200026Q0002000100014Q000200036Q00020001000100122Q000200013Q00202Q0002000200024Q000300043Q00122Q000400033Q00122Q000500046Q000300056Q00023Q000300062Q000200F700013Q00049E3Q00F7000100066D000300F700013Q00049E3Q00F7000100122Q000400053Q001248000500063Q00202Q00060005000700202Q00060006000800202Q00060006000900122Q0008000A6Q00060008000200202Q00070005000700202Q00070007000800202Q00070007000B00122Q0009000C6Q00070009000200202Q00080005000700202Q00080008000D00202Q00080008000E00122Q000A000A6Q0008000A00024Q000900063Q000E2Q000F002B0001000900049E3Q002B00012Q000F010900053Q00203E0009000900102Q0022000A00063Q0010A700090011000A2Q0022000900073Q000E0C010F00320001000900049E3Q003200012Q000F010900053Q00203E0009000900102Q0022000A00073Q0010A700090012000A2Q0022000900083Q000E0C010F00390001000900049E3Q003900012Q000F010900053Q00203E0009000900102Q0022000A00083Q0010A700090013000A00203E00090004001400066D000900A300013Q00049E3Q00A3000100203E0009000400140020D90009000900152Q00F000090002000200066D000900A300013Q00049E3Q00A300010012090109000F4Q002Q010A000A3Q0026B5000900960001001600049E3Q0096000100066D000A008A00013Q00049E3Q008A0001001209010B000F4Q002Q010C000C3Q000EF3000F00490001000B00049E3Q0049000100122Q000D00173Q002016010D000D00184Q000E000A6Q000D000200024Q000C000D3Q00062Q000C007C00013Q00049E3Q007C000100203E000D000C001900066D000D007C00013Q00049E3Q007C0001001209010D000F4Q002Q010E000E3Q0026B5000D00570001000F00049E3Q0057000100203E000E000C0019001211010F001A6Q001000043Q00122Q0011001B3Q00122Q0012001C6Q001000126Q000F3Q000200062Q000F006E0001000E00049E3Q006E0001001209010F000F3Q0026B5000F00630001000F00049E3Q006300012Q000F011000053Q00206100100010001000302Q0010001D001E4Q001000053Q00202Q00100010001000302Q0010001F002000044Q00B4000100049E3Q0063000100049E3Q00B40001001209010F000F3Q0026B5000F006F0001000F00049E3Q006F00012Q000F011000053Q00206100100010001000302Q0010001D00204Q001000053Q00202Q00100010001000302Q0010001F001E00044Q00B4000100049E3Q006F000100049E3Q00B4000100049E3Q0057000100049E3Q00B40001001209010D000F3Q0026B5000D007D0001000F00049E3Q007D00012Q000F010E00053Q002061000E000E001000302Q000E001D00204Q000E00053Q00202Q000E000E001000302Q000E001F002000044Q00B4000100049E3Q007D000100049E3Q00B4000100049E3Q0049000100049E3Q00B40001001209010B000F3Q0026B5000B008B0001000F00049E3Q008B00012Q000F010C00053Q002061000C000C001000302Q000C001D00204Q000C00053Q00202Q000C000C001000302Q000C001F002000044Q00B4000100049E3Q008B000100049E3Q00B400010026B5000900430001000F00049E3Q004300012Q000F010B00053Q00200E000B000B001000202Q000C0004001400202Q000C000C002200102Q000B0021000C4Q000B00053Q00202Q000B000B001000202Q000A000B002300122Q000900163Q00044Q0043000100049E3Q00B400010012090109000F3Q0026B5000900AD0001000F00049E3Q00AD00012Q000F010A00053Q00200B010A000A001000302Q000A0021000F4Q000A00053Q00202Q000A000A001000302Q000A001D002000122Q000900163Q0026B5000900A40001001600049E3Q00A400012Q000F010A00053Q00203E000A000A0010003089000A001F002000049E3Q00B4000100049E3Q00A4000100203E00090004002400066D000900EC00013Q00049E3Q00EC000100203E0009000400240020D90009000900152Q00F000090002000200066D000900EC00013Q00049E3Q00EC00010012090109000F4Q002Q010A000C3Q0026B5000900D30001001600049E3Q00D3000100203E000D0004002400203E000D000D002200066D000D00CF00013Q00049E3Q00CF00012Q000F010D00053Q00203E000D000D001000203E000D000D00250006D7000D00CF0001000100049E3Q00CF00012Q000F010D00053Q00207A000D000D001000202Q000E0004002400202Q000E000E002200102Q000D0026000E00044Q00F700012Q000F010D00053Q00203E000D000D0010003089000D0026000F00049E3Q00F700010026B5000900BE0001000F00049E3Q00BE000100203E000D00040024002072000D000D002700202Q000D000D00284Q000D0002000F4Q000C000F6Q000B000E6Q000A000D3Q00262Q000B00E60001001600049E3Q00E60001000E0C012900E60001000B00049E3Q00E6000100260E010C00E60001001600049E3Q00E600012Q000F010D00053Q00203E000D000D0010003089000D0025001E00049E3Q00E900012Q000F010D00053Q00203E000D000D0010003089000D00250020001209010900163Q00049E3Q00BE000100049E3Q00F700010012090109000F3Q0026B5000900ED0001000F00049E3Q00ED00012Q000F010A00053Q002061000A000A001000302Q000A0026000F4Q000A00053Q00202Q000A000A001000302Q000A0025002000044Q00F7000100049E3Q00ED000100122Q0004002A3Q00122Q0005002A3Q00203E00050005002B0006D7000500FD0001000100049E3Q00FD00012Q008300055Q0010A70004002B000500122Q0004002A3Q00122Q0005002A3Q00203E00050005002C0006D7000500042Q01000100049E3Q00042Q012Q008300055Q0010A70004002C000500122Q0004002A3Q00122Q0005002A3Q00203E00050005002D0006D70005000B2Q01000100049E3Q000B2Q012Q008300055Q0010A70004002D000500122Q0004002A3Q00122Q0005002A3Q00203E00050005002E0006D7000500122Q01000100049E3Q00122Q012Q008300055Q0010A70004002E00050002B900045Q0002B9000500013Q0002B9000600023Q0002B9000700033Q0012080108002F3Q00202Q00080008003000122Q000900316Q00080002000200202Q00090008003200202Q000A0008003300122Q000B00343Q00122Q000C00356Q000D00043Q00122Q000E00363Q00122Q000F00376Q000D000F6Q000C8Q000B3Q000200122Q000C00386Q000C0001000F4Q0010000F000B00122Q001100396Q001200043Q00122Q0013003A3Q00122Q0014003B6Q001200146Q00113Q001900122Q001A003C6Q001B00043Q00122Q001C003D3Q00122Q001D003E6Q001B001D6Q001A3Q002100122Q002200013Q00202Q0022002200024Q002300043Q00122Q0024003F3Q00122Q002500406Q002300256Q00223Q002300062Q0022007F2Q013Q00049E3Q007F2Q0100066D0023007F2Q013Q00049E3Q007F2Q0100122Q002400413Q00066D0024004A2Q013Q00049E3Q004A2Q0100122Q002400413Q00207100240024004200202Q00240024004300202Q00240024004400202Q00240024004500202Q00240024004600062Q0024004B2Q01000100049E3Q004B2Q01001209012400474Q000501256Q00B1002600043Q00122Q002700483Q00122Q002800496Q00260028000200062Q002400582Q01002600049E3Q00582Q012Q000F012600043Q0012090127004A3Q0012090128004B4Q00790026002800020006FE002400592Q01002600049E3Q00592Q012Q0005012500014Q008300263Q00010030890026004C001E0006E300270004000100012Q00FD3Q00263Q0006E3002800050001000C2Q000F012Q00044Q00FD3Q00254Q00FD3Q00064Q00FD3Q00274Q00FD3Q00074Q00FD3Q000A4Q00FD3Q00104Q000F012Q00054Q00FD3Q00044Q00FD3Q00154Q00FD3Q00054Q00FD3Q001E4Q00F6002900286Q00290001000200202Q002A0029004D00202Q002B0029004E00122Q002C002A3Q00202Q002C002C002B00062Q002C007D2Q013Q00049E3Q007D2Q01001209012C000F3Q0026B5002C00732Q01000F00049E3Q00732Q0100122Q002D002A3Q002096002D002D002B00102Q002D004D002A00122Q002D002A3Q00202Q002D002D002B00102Q002D004E002B00044Q007D2Q0100049E3Q00732Q012Q007500245Q00049E3Q008E2Q0100122Q0024002A3Q00203E00240024002B00066D0024008E2Q013Q00049E3Q008E2Q010012090124000F3Q0026B5002400842Q01000F00049E3Q00842Q0100122Q0025002A3Q00207D00250025002B00302Q0025004D000F00122Q0025002A3Q00202Q00250025002B00302Q0025004E000F00044Q008E2Q0100049E3Q00842Q010006E3002400060001000A2Q00FD3Q00064Q00FD3Q00074Q00FD3Q000A4Q00FD3Q00104Q000F012Q00044Q000F012Q00054Q00FD3Q00044Q00FD3Q00154Q00FD3Q00054Q00FD3Q001E3Q00066D000200B92Q013Q00049E3Q00B92Q0100066D000300B92Q013Q00049E3Q00B92Q010012090125000F4Q002Q012600283Q000EF3001600A62Q01002500049E3Q00A62Q012Q00FD002900264Q00670029000100022Q00FD002700294Q00FD002800273Q0012090125004F3Q0026B5002500AD2Q01000F00049E3Q00AD2Q012Q002Q012600263Q0006E300260007000100022Q00FD3Q00244Q000F012Q00053Q001209012500163Q0026B50025009F2Q01004F00049E3Q009F2Q0100122Q0029002A3Q00203E00290029002C00066D002900C02Q013Q00049E3Q00C02Q0100122Q0029002A3Q00203E00290029002C0010A700290026002800049E3Q00C02Q0100049E3Q009F2Q0100049E3Q00C02Q0100122Q0025002A3Q00203E00250025002C00066D002500C02Q013Q00049E3Q00C02Q0100122Q0025002A3Q00203E00250025002C00308900250026000F00122Q002500013Q0020030125002500024Q002600043Q00122Q002700503Q00122Q002800516Q002600286Q00253Q002600062Q002500E52Q013Q00049E3Q00E52Q0100066D002600E52Q013Q00049E3Q00E52Q010012090127000F4Q002Q0128002A3Q000EF3004F00D72Q01002700049E3Q00D72Q0100122Q002B002A3Q00203E002B002B002D00066D002B00E52Q013Q00049E3Q00E52Q0100122Q002B002A3Q00203E002B002B002D0010A7002B0026002A00049E3Q00E52Q010026B5002700DD2Q01000F00049E3Q00DD2Q012Q002Q012800283Q0006E300280008000100012Q00FD3Q00243Q001209012700163Q000EF3001600CD2Q01002700049E3Q00CD2Q012Q00FD002B00284Q0073002B000100024Q0029002B6Q002A00293Q00122Q0027004F3Q00044Q00CD2Q0100122Q002700013Q0020030127002700024Q002800043Q00122Q002900523Q00122Q002A00536Q0028002A6Q00273Q002800062Q0027000A02013Q00049E3Q000A020100066D0028000A02013Q00049E3Q000A02010012090129000F4Q002Q012A002C3Q0026B5002900FC2Q01004F00049E3Q00FC2Q0100122Q002D002A3Q00203E002D002D002E00066D002D000A02013Q00049E3Q000A020100122Q002D002A3Q00203E002D002D002E0010A7002D0026002C00049E3Q000A02010026B5002900030201001600049E3Q000302012Q00FD002D002A4Q0067002D000100022Q00FD002B002D4Q00FD002C002B3Q0012090129004F3Q0026B5002900F22Q01000F00049E3Q00F22Q012Q002Q012A002A3Q0006E3002A0009000100012Q00FD3Q00243Q001209012900163Q00049E3Q00F22Q012Q000F012900053Q0020B200290029005400122Q002A00563Q00202Q002A002A00574Q002B00043Q00122Q002C00583Q00122Q002D00596Q002B002D00024Q002A002A002B00062Q002A00160201000100049E3Q00160201001209012A00473Q0010A700290055002A00066D0022007302013Q00049E3Q0073020100066D0023007302013Q00049E3Q007302012Q000F012900053Q00201C01290029005400202Q0029002900554Q002A00043Q00122Q002B005A3Q00122Q002C005B6Q002A002C000200062Q002900730201002A00049E3Q007302010012090129000F3Q0026B5002900430201000F00049E3Q004302012Q000F012A00053Q00209F002A002A005400122Q002B002A3Q00202Q002B002B002B00202Q002B002B004D00102Q002A0026002B4Q002A00053Q00202Q002A002A005400122Q002B005D3Q00202Q002B002B005E00202Q002B002B001600202Q002B002B005F00262Q002B003F0201006000049E3Q003F020100122Q002B005D3Q002032002B002B005E00202Q002B002B001600202Q002B002B005F4Q002C00043Q00122Q002D00613Q00122Q002E00626Q002C002E000200062Q002B00400201002C00049E3Q004002012Q00C3002B6Q0005012B00013Q0010A7002A005C002B001209012900163Q0026B50029005E0201004F00049E3Q005E02012Q000F012A00053Q0020EB002A002A005400122Q002B00643Q00202Q002B002B006500122Q002C002A3Q00202Q002C002C006600202Q002C002C006700122Q002D00683Q00202Q002D002D006900202Q002D002D006A4Q002B002D000200102Q002A0063002B4Q002A00053Q00202Q002A002A005400122Q002B00643Q00202Q002B002B006500122Q002C002A3Q00202Q002C002C006600202Q002C002C006C00122Q002D00683Q00202Q002D002D006900202Q002D002D006A4Q002B002D000200102Q002A006B002B00044Q00870301000EF3001600250201002900049E3Q002502012Q000F012A00053Q002047002A002A005400122Q002B00683Q00202Q002B002B006900202Q002B002B006E00202Q002B002B006F00102Q002A006D002B4Q002A00053Q00202Q002A002A005400122Q002B00683Q00202Q002B002B006900202Q002B002B007100062Q002B006F0201000100049E3Q006F0201001209012B000F3Q0010A7002A0070002B0012090129004F3Q00049E3Q0025020100049E3Q0087030100066D000200BE02013Q00049E3Q00BE020100066D000300BE02013Q00049E3Q00BE02012Q000F012900053Q00201C01290029005400202Q0029002900554Q002A00043Q00122Q002B00723Q00122Q002C00736Q002A002C000200062Q002900BE0201002A00049E3Q00BE02010012090129000F3Q0026B5002900900201000F00049E3Q009002012Q000F012A00053Q002062002A002A005400122Q002B002A3Q00202Q002B002B002C00202Q002B002B002600102Q002A0026002B4Q002A00053Q00202Q002A002A005400122Q002B00563Q00202Q002B002B001000202Q002B002B001F00102Q002A005C002B00122Q002900163Q000EF3001600A10201002900049E3Q00A102012Q000F012A00053Q002094002A002A005400122Q002B00743Q00202Q002B002B007500202Q002B002B001600102Q002A006D002B4Q002A00053Q00202Q002A002A005400122Q002B00063Q00202Q002B002B007600062Q002B009F0201000100049E3Q009F0201001209012B000F3Q0010A7002A0070002B0012090129004F3Q0026B5002900810201004F00049E3Q008102012Q000F012A00053Q0020EB002A002A005400122Q002B00643Q00202Q002B002B006500122Q002C002A3Q00202Q002C002C006600202Q002C002C006700122Q002D00563Q00202Q002D002D001000202Q002D002D00114Q002B002D000200102Q002A0063002B4Q002A00053Q00202Q002A002A005400122Q002B00643Q00202Q002B002B006500122Q002C002A3Q00202Q002C002C006600202Q002C002C006C00122Q002D00563Q00202Q002D002D001000202Q002D002D00124Q002B002D000200102Q002A006B002B00044Q0087030100049E3Q0081020100049E3Q0087030100066D0025001E03013Q00049E3Q001E030100066D0026001E03013Q00049E3Q001E03012Q000F012900053Q00201C01290029005400202Q0029002900554Q002A00043Q00122Q002B00773Q00122Q002C00786Q002A002C000200062Q0029001E0301002A00049E3Q001E03010012090129000F4Q002Q012A002C3Q0026B5002900E40201007900049E3Q00E402012Q000F012D00053Q0020CE002D002D005400122Q002E00643Q00202Q002E002E006500122Q002F002A3Q00202Q002F002F006600202Q002F002F00674Q0030002A6Q002E0030000200102Q002D0063002E4Q002D00053Q00202Q002D002D005400122Q002E00643Q00202Q002E002E006500122Q002F002A3Q00202Q002F002F006600202Q002F002F006C4Q0030002C6Q002E0030000200102Q002D006B002E00044Q008703010026B5002900F90201004F00049E3Q00F9020100122Q002D007A3Q00204C002D002D007B4Q002F00043Q00122Q0030007C3Q00122Q0031007D6Q002F00316Q002D3Q002E4Q002B002E6Q002A002D3Q00122Q002D007A3Q00202Q002D002D007B4Q002F00043Q00122Q0030007E3Q00122Q0031007F6Q002F00316Q002D3Q002E4Q002B002E6Q002C002D3Q00122Q002900793Q000EF3000F00050301002900049E3Q000503012Q000F012D00053Q0020EA002D002D005400122Q002E002A3Q00202Q002E002E002D00202Q002E002E002600102Q002D0026002E4Q002D00053Q00202Q002D002D005400302Q002D005C002000122Q002900163Q0026B5002900CD0201001600049E3Q00CD02012Q000F012D00053Q00209C002D002D005400122Q002E00803Q00202Q002E002E00154Q002E0002000200062Q002E00110301000100049E3Q0011030100122Q002E00813Q0020D9002E002E00152Q00F0002E000200020010A7002D006D002E2Q00D8002D00053Q00202Q002D002D005400122Q002E007A3Q00202Q002E002E00824Q002E0001000200062Q002E001A0301000100049E3Q001A0301001209012E000F3Q0010A7002D0070002E0012090129004F3Q00049E3Q00CD020100049E3Q0087030100066D0027006403013Q00049E3Q0064030100066D0028006403013Q00049E3Q006403012Q000F012900053Q00201C01290029005400202Q0029002900554Q002A00043Q00122Q002B00833Q00122Q002C00846Q002A002C000200062Q002900640301002A00049E3Q006403010012090129000F3Q000EF30016003B0301002900049E3Q003B03012Q000F012A00053Q002057002A002A005400302Q002A006D001E4Q002A00053Q00202Q002A002A005400122Q002B00853Q00202Q002B002B00824Q002B0001000200062Q002B00390301000100049E3Q00390301001209012B000F3Q0010A7002A0070002B0012090129004F3Q0026B5002900560301004F00049E3Q005603012Q000F012A00053Q00208A002A002A005400122Q002B00643Q00202Q002B002B006500122Q002C002A3Q00202Q002C002C006600202Q002C002C006700122Q002D00853Q00202Q002D002D00864Q002D002E6Q002B3Q000200102Q002A0063002B4Q002A00053Q00202Q002A002A005400122Q002B00643Q00202Q002B002B006500122Q002C002A3Q00202Q002C002C006600202Q002C002C006C00122Q002D00853Q00202Q002D002D00864Q002D002E6Q002B3Q000200102Q002A006B002B00044Q00870301000EF3000F002C0301002900049E3Q002C03012Q000F012A00053Q002036002A002A005400122Q002B002A3Q00202Q002B002B002E00202Q002B002B002600102Q002A0026002B4Q002A00053Q00202Q002A002A005400302Q002A005C002000122Q002900163Q00044Q002C030100049E3Q008703010012090129000F3Q000EF3000F006E0301002900049E3Q006E03012Q000F012A00053Q00200B012A002A005400302Q002A0026000F4Q002A00053Q00202Q002A002A005400302Q002A005C002000122Q002900163Q0026B5002900770301001600049E3Q007703012Q000F012A00053Q00200B012A002A005400302Q002A006D00204Q002A00053Q00202Q002A002A005400302Q002A0070000F00122Q0029004F3Q0026B5002900650301004F00049E3Q006503012Q000F012A00053Q002059002A002A005400122Q002B002A3Q00202Q002B002B006600202Q002B002B006700102Q002A0063002B4Q002A00053Q00202Q002A002A005400122Q002B002A3Q00202Q002B002B006600202Q002B002B006C00102Q002A006B002B00044Q0087030100049E3Q006503012Q000F012900053Q0020530029002900544Q002A00066Q002B00043Q00122Q002C00883Q00122Q002D00896Q002B002D6Q002A3Q000200102Q00290087002A6Q00013Q000A3Q00033Q00028Q0003073Q0047657454696D65025Q00408F40010E3Q0012092Q0100013Q0026B5000100010001000100049E3Q0001000100066D3Q000A00013Q00049E3Q000A000100122Q000200024Q00670002000100020020070002000200033Q0001023Q00022Q007E000200024Q002Q010200024Q007E000200023Q00049E3Q000100012Q003F3Q00017Q00033Q00028Q0003073Q0047657454696D65025Q00408F40010E3Q0012092Q0100013Q0026B5000100010001000100049E3Q0001000100066D3Q000A00013Q00049E3Q000A000100122Q000200024Q00670002000100020020070002000200033Q0001023Q00022Q007E000200024Q002Q010200024Q007E000200023Q00049E3Q000100012Q003F3Q00017Q00083Q00028Q0003073Q00435F5370652Q6C03103Q004765745370652Q6C432Q6F6C646F776E0003093Q00737461727454696D6503083Q006475726174696F6E03073Q0047657454696D65025Q00408F40011B3Q0012092Q0100014Q002Q010200023Q0026B5000100020001000100049E3Q0002000100122Q000300023Q0020230003000300034Q00048Q0003000200024Q000200033Q00262Q000200170001000400049E3Q0017000100203E00030002000500261D000300170001000400049E3Q0017000100203E000300020006001214010400076Q00040001000200202Q0005000200054Q0004000400054Q00030003000400202Q00030003000800062Q000300180001000100049E3Q00180001001209010300014Q007E000300023Q00049E3Q000200012Q003F3Q00017Q00053Q00028Q0003063Q00435F4974656D030F3Q004765744974656D432Q6F6C646F776E03073Q0047657454696D65025Q00408F4001183Q0012092Q0100014Q002Q010200043Q0026B5000100020001000100049E3Q0002000100122Q000500023Q0020A10005000500034Q00068Q0005000200074Q000400076Q000300066Q000200053Q00262Q000200140001000100049E3Q0014000100122Q000500044Q001F0005000100024Q0005000500024Q00050003000500202Q00050005000500062Q000500150001000100049E3Q00150001001209010500014Q007E000500023Q00049E3Q000200012Q003F3Q00017Q00023Q00028Q0003053Q00706169727301113Q0012092Q0100013Q0026B5000100010001000100049E3Q0001000100122Q000200024Q000F01036Q002500020002000400049E3Q000B00010006FE0005000B00013Q00049E3Q000B00012Q000501076Q007E000700023Q000663000200070001000200049E3Q000700012Q0005010200014Q007E000200023Q00049E3Q000100012Q003F3Q00017Q00133Q0003073Q004AF4EC35515D0D03073Q00741A868558302F03063Q0048656B696C69030B3Q00446973706C6179502Q6F6C03073Q005072696D617279030F3Q005265636F2Q6D656E646174696F6E732Q033Q003FEE8503063Q00127EA1C084DD2Q033Q00414F4503073Q006F3AA709574D3103053Q00363F48CE6403083Q006E756D49636F6E73028Q002Q033Q00E9766003063Q001BA839251A8503073Q001DB875A5D63FB303053Q00B74DCA1CC82Q033Q00361CAC03043Q00687753E900684Q00E45Q00024Q00015Q00122Q000200013Q00122Q000300026Q00010003000200122Q000200033Q00062Q0002000E00013Q00049E3Q000E000100122Q000200033Q00203E00020002000400203E00020002000500203E0002000200060006D70002000F0001000100049E3Q000F00012Q008300026Q009D3Q000100022Q00D400015Q00122Q000200073Q00122Q000300086Q00010003000200122Q000200033Q00062Q0002002000013Q00049E3Q002000012Q000F010200013Q00066D0002002000013Q00049E3Q0020000100122Q000200033Q00203E00020002000400203E00020002000900203E0002000200060006D7000200210001000100049E3Q002100012Q008300026Q009D3Q000100022Q00E400013Q00024Q00025Q00122Q0003000A3Q00122Q0004000B6Q00020004000200122Q000300033Q00062Q0003003000013Q00049E3Q0030000100122Q000300033Q00203E00030003000400203E00030003000500203E00030003000C0006D7000300310001000100049E3Q003100010012090103000D4Q009D0001000200032Q00D400025Q00122Q0003000E3Q00122Q0004000F6Q00020004000200122Q000300033Q00062Q0003004200013Q00049E3Q004200012Q000F010300013Q00066D0003004200013Q00049E3Q0042000100122Q000300033Q00203E00030003000400203E00030003000900203E00030003000C0006D7000300430001000100049E3Q004300010012090103000D4Q009D0001000200032Q001600023Q00024Q00035Q00122Q000400103Q00122Q000500116Q00030005000200202Q00020003000D4Q00035Q00122Q000400123Q00122Q000500136Q00030005000200202Q00020003000D0006E300033Q0001000B2Q000F017Q000F012Q00024Q000F012Q00034Q000F012Q00044Q000F012Q00054Q000F012Q00064Q000F012Q00074Q000F012Q00084Q000F012Q00094Q000F012Q000A4Q000F012Q000B4Q0026000400033Q00202Q00053Q00054Q00040002000200102Q0002000500044Q000400013Q00062Q0004006600013Q00049E3Q006600012Q00FD000400033Q00203E00053Q00092Q00F00004000200020010A70002000900042Q007E000200024Q003F3Q00013Q00013Q00413Q00028Q00026Q00F03F03083Q00616374696F6E494403043Q0077616974025Q00408F4003093Q00696E64696361746F7203053Q00F6E1242E4603053Q00239598474203063Q0048656B696C6903053Q00537461746503083Q0073652Q74696E677303043Q007370656303053Q006379636C652Q0103113Q004C6567656E6461727953652Q74696E677303083Q0053652Q74696E677303093Q0018FD56BF1900EB4EB503053Q005A798822D0030E3Q004973506C617965724D6F76696E67023Q00402244634103053Q00436C612Q7303093Q006162696C697469657303043Q006974656D026Q001040027Q0040026Q000840026Q001840026Q001C4003143Q00476574496E76656E746F72794974656D4C696E6B03063Q00D7025407C21C03043Q007EA76E35026Q002A4003063Q002D1C2FE1D92D03063Q005F5D704E98BC026Q002C4003063Q00D1F9840CE1AC03073Q00B2A195E57584DE026Q00304003063Q00435F4974656D03123Q004765744974656D496E666F496E7374616E7403063Q0098D7DCB5A40403083Q0043E8BBBDCCC176C6026Q00314003063Q009B22B4393E1003073Q008FEB4ED5405B62026Q002E4003063Q009D4485F075A403063Q00D6ED28E48910026Q00244003023Q00444203073Q0070726F66696C6503073Q00746F2Q676C657303073Q00706F74696F6E7303053Q0076616C7565030D3Q00A1D3DCE90CB28CECE1F702AB8003063Q00C6E5838FB963030C3Q004765744974656D436F756E7403063Q0073656C656374030B3Q004765744974656D496E666F03043Q006D6174682Q033Q00616273026Q00144003073Q00435F5370652Q6C030D3Q0049735370652Q6C557361626C65000150012Q0012092Q0100014Q002Q010200023Q000EF3000200462Q01000100049E3Q00462Q0100066D0002004F2Q013Q00049E3Q004F2Q0100203E00030002000300066D0003004F2Q013Q00049E3Q004F2Q0100203E00030002000300203300040002000400202Q00040004000500202Q0005000200064Q00065Q00122Q000700073Q00122Q000800086Q00060008000200062Q000500230001000600049E3Q0023000100122Q000500093Q00206F00050005000A00202Q00050005000B00202Q00050005000C00202Q00050005000D00262Q000500230001000E00049E3Q0023000100122Q0005000F3Q0020A00005000500104Q00065Q00122Q000700113Q00122Q000800126Q0006000800024Q00050005000600262Q000500240001000E00049E3Q002400012Q00C300056Q0005010500013Q0012C8000600136Q0006000100024Q000700016Q000800036Q00070002000200062Q0005003400013Q00049E3Q003400012Q000F010800024Q00FD000900034Q00F000080002000200066D0008003400013Q00049E3Q00340001001209010800144Q007E000800023Q00049E3Q00432Q0100260E0103001F2Q01000100049E3Q001F2Q0100122Q000800093Q00203E00080008001500203E0008000800162Q003800080008000300066D000800D800013Q00049E3Q00D8000100203E00090008001700066D000900D800013Q00049E3Q00D800012Q000F010900033Q00203E000A000800172Q00F00009000200020026F9000900D80001000200049E3Q00D800012Q000F010900045Q000109000700092Q000F010A00053Q00066A000900D80001000A00049E3Q00D80001001209010900014Q002Q010A00163Q0026B5000900710001001800049E3Q007100012Q002Q011600163Q00203E0017000800170006FE001000530001001700049E3Q00530001001209011600023Q00049E3Q006D000100203E0017000800170006FE001100580001001700049E3Q00580001001209011600193Q00049E3Q006D000100203E0017000800170006FE0012005D0001001700049E3Q005D00010012090116001A3Q00049E3Q006D000100203E0017000800170006FE001300620001001700049E3Q00620001001209011600183Q00049E3Q006D000100203E0017000800170006FE001400670001001700049E3Q006700010012090116001B3Q00049E3Q006D000100203E0017000800170006FE0015006C0001001700049E3Q006C00010012090116001C3Q00049E3Q006D000100203E00160008001700066D001600D800013Q00049E3Q00D800012Q007E001600023Q00049E3Q00D800010026B50009008C0001000100049E3Q008C000100122Q0017001D4Q002900185Q00122Q0019001E3Q00122Q001A001F6Q0018001A000200122Q001900206Q0017001900024Q000A00173Q00122Q0017001D6Q00185Q00122Q001900213Q00122Q001A00226Q0018001A000200122Q001900236Q0017001900024Q000B00173Q00122Q0017001D6Q00185Q00122Q001900243Q00122Q001A00256Q0018001A000200122Q001900266Q0017001900024Q000C00173Q00122Q000900023Q0026B5000900A40001001900049E3Q00A40001000618001000950001000A00049E3Q0095000100122Q001700273Q00203E0017001700282Q00FD0018000A4Q00F00017000200022Q00FD001000173Q0006180011009C0001000B00049E3Q009C000100122Q001700273Q00203E0017001700282Q00FD0018000B4Q00F00017000200022Q00FD001100173Q000618001200A30001000C00049E3Q00A3000100122Q001700273Q00203E0017001700282Q00FD0018000C4Q00F00017000200022Q00FD001200173Q0012090109001A3Q0026B5000900BC0001001A00049E3Q00BC0001000618001300AD0001000D00049E3Q00AD000100122Q001700273Q00203E0017001700282Q00FD0018000D4Q00F00017000200022Q00FD001300173Q000618001400B40001000E00049E3Q00B4000100122Q001700273Q00203E0017001700282Q00FD0018000E4Q00F00017000200022Q00FD001400173Q000618001500BB0001000F00049E3Q00BB000100122Q001700273Q00203E0017001700282Q00FD0018000F4Q00F00017000200022Q00FD001500173Q001209010900183Q0026B50009004B0001000200049E3Q004B000100122Q0017001D4Q000500185Q00122Q001900293Q00122Q001A002A6Q0018001A000200122Q0019002B6Q0017001900024Q000D00173Q00122Q0017001D6Q00185Q00122Q0019002C3Q00122Q001A002D6Q0018001A000200122Q0019002E6Q0017001900024Q000E00173Q00122Q0017001D6Q00185Q00122Q0019002F3Q00122Q001A00306Q0018001A000200122Q001900316Q0017001900024Q000F00173Q00122Q000900193Q00044Q004B000100122Q000900093Q0020E200090009003200202Q00090009003300202Q00090009003400202Q00090009003500202Q00090009003600062Q000900432Q013Q00049E3Q00432Q01001209010A00014Q002Q010B000C3Q0026B5000A00F10001000100049E3Q00F100012Q000F010D00063Q002082000D000D00104Q000E5Q00122Q000F00373Q00122Q001000386Q000E001000022Q00A3000B000D000E00122Q000D00273Q00202Q000D000D00394Q000E000B6Q000D000200024Q000C000D3Q00122Q000A00023Q0026B5000A00E20001000200049E3Q00E20001000E0C2Q0100432Q01000C00049E3Q00432Q01001209010D00014Q002Q010E000F3Q000EF3000100092Q01000D00049E3Q00092Q0100122Q0010003A3Q00125E001100193Q00122Q001200273Q00202Q00120012003B4Q0013000B6Q001200136Q00103Q00024Q000E00103Q00062Q000F00082Q01000E00049E3Q00082Q0100122Q001000273Q00203E0010001000282Q00FD0011000E4Q00F00010000200022Q00FD000F00103Q001209010D00023Q0026B5000D00F70001000200049E3Q00F7000100066D000F00432Q013Q00049E3Q00432Q0100122Q0010003C3Q00203E00100010003D2Q00FD001100034Q00F00010000200020006FE000F00432Q01001000049E3Q00432Q012Q000F011000034Q00FD0011000F4Q00F00010000200020026F9001000432Q01003100049E3Q00432Q010012090110003E4Q007E001000023Q00049E3Q00432Q0100049E3Q00F7000100049E3Q00432Q0100049E3Q00E2000100049E3Q00432Q01000E0C2Q0100432Q01000300049E3Q00432Q0100122Q0008003F3Q00203E0008000800402Q00FD000900034Q00F000080002000200066D000800432Q013Q00049E3Q00432Q012Q000F010800045Q000108000700082Q000F010900053Q00066A000800432Q01000900049E3Q00432Q012Q000F010800074Q000F010900084Q00F000080002000200261D000800372Q01004100049E3Q00372Q012Q000F010800074Q000F010900084Q00F00008000200022Q000F010900053Q00066A000800432Q01000900049E3Q00432Q012Q000F010800094Q000F0109000A4Q00F000080002000200261D000800422Q01004100049E3Q00422Q012Q000F010800094Q000F0109000A4Q00F00008000200022Q000F010900053Q00066A000800432Q01000900049E3Q00432Q012Q007E000300023Q001209010800014Q007E000800023Q00049E3Q004F2Q01000EF3000100020001000100049E3Q000200012Q002Q010200023Q00203E00033Q000200066D0003004D2Q013Q00049E3Q004D2Q0100203E00023Q00020012092Q0100023Q00049E3Q000200012Q003F3Q00017Q00283Q00028Q0003143Q00476574496E76656E746F72794974656D4C696E6B03063Q004180A96A549E03043Q001331ECC8026Q002A4003063Q00EE3BF7AEE1A803063Q00DA9E5796D784026Q002C4003063Q00EB12D8FB333003073Q00AD9B7EB9825642026Q00304003063Q00F5AABBDE8DFE03063Q008C85C6DAA7E8026Q003140026Q00F03F026Q000840027Q0040026Q001040026Q001840026Q001C4003083Q0053652Q74696E6773030D3Q00911E874D8BA127BB73AAB423B103053Q00E4D54ED41D03063Q00435F4974656D03123Q004765744974656D496E666F496E7374616E74030C3Q004765744974656D436F756E7403063Q0073656C656374030B3Q004765744974656D496E666F03043Q006D6174682Q033Q00616273026Q002440026Q00144003063Q009740B71CEE9503053Q008BE72CD665026Q002E4003063Q00C9E3074715A303083Q0076B98F663E70D15103073Q00435F5370652Q6C030D3Q0049735370652Q6C557361626C650001F33Q00066D3Q00F200013Q00049E3Q00F200012Q00FD00016Q000F01026Q00FD000300014Q00F0000200020002000E0C2Q0100CC0001000100049E3Q00CC00012Q000F010300014Q001D010400016Q0003000200024Q000400026Q0003000300044Q000400033Q00062Q000300CC0001000400049E3Q00CC0001001209010300014Q002Q010400123Q0026B5000300350001000100049E3Q0035000100122Q001300024Q00FB001400043Q00122Q001500033Q00122Q001600046Q00140016000200122Q001500056Q0013001500024Q000400133Q00122Q001300026Q001400043Q00122Q001500063Q00122Q001600076Q00140016000200122Q001500086Q0013001500024Q000500133Q00122Q001300026Q001400043Q00122Q001500093Q00122Q0016000A6Q00140016000200122Q0015000B6Q0013001500024Q000600133Q00122Q001300026Q001400043Q00122Q0015000C3Q00122Q0016000D6Q00140016000200122Q0015000E6Q0013001500024Q000700133Q00122Q0003000F3Q000EF30010005A0001000300049E3Q005A00012Q002Q011000103Q0006FE000A003C0001000100049E3Q003C00010012090110000F3Q00049E3Q004F00010006FE000B00400001000100049E3Q00400001001209011000113Q00049E3Q004F00010006FE000C00440001000100049E3Q00440001001209011000103Q00049E3Q004F00010006FE000D00480001000100049E3Q00480001001209011000123Q00049E3Q004F00010006FE000E004C0001000100049E3Q004C0001001209011000133Q00049E3Q004F00010006FE000F004F0001000100049E3Q004F0001001209011000143Q00066D0010005200013Q00049E3Q005200012Q007E001000024Q000F011300053Q0020820013001300154Q001400043Q00122Q001500163Q00122Q001600176Q0014001600022Q0038001100130014001209010300123Q0026B5000300790001001100049E3Q00790001000618000C00630001000600049E3Q0063000100122Q001300183Q00203E0013001300192Q00FD001400064Q00F00013000200022Q00FD000C00133Q000618000D006A0001000700049E3Q006A000100122Q001300183Q00203E0013001300192Q00FD001400074Q00F00013000200022Q00FD000D00133Q000618000E00710001000800049E3Q0071000100122Q001300183Q00203E0013001300192Q00FD001400084Q00F00013000200022Q00FD000E00133Q000618000F00780001000900049E3Q0078000100122Q001300183Q00203E0013001300192Q00FD001400094Q00F00013000200022Q00FD000F00133Q001209010300103Q0026B5000300AA0001001200049E3Q00AA000100122Q001300183Q00200400130013001A4Q001400116Q0013000200024Q001200133Q000E2Q000100CC0001001200049E3Q00CC0001001209011300014Q002Q011400153Q000EF3000100960001001300049E3Q0096000100122Q0016001B3Q00125E001700113Q00122Q001800183Q00202Q00180018001C4Q001900116Q001800196Q00163Q00024Q001400163Q00062Q001500950001001400049E3Q0095000100122Q001600183Q00203E0016001600192Q00FD001700144Q00F00016000200022Q00FD001500163Q0012090113000F3Q0026B5001300840001000F00049E3Q0084000100066D001500CC00013Q00049E3Q00CC000100122Q0016001D3Q00203E00160016001E2Q00FD001700014Q00F00016000200020006FE001500CC0001001600049E3Q00CC00012Q000F011600014Q00FD001700154Q00F00016000200020026F9001600CC0001001F00049E3Q00CC0001001209011600204Q007E001600023Q00049E3Q00CC000100049E3Q0084000100049E3Q00CC00010026B5000300120001000F00049E3Q0012000100122Q001300024Q00D5001400043Q00122Q001500213Q00122Q001600226Q00140016000200122Q001500236Q0013001500024Q000800133Q00122Q001300026Q001400043Q00122Q001500243Q00122Q001600256Q00140016000200122Q0015001F6Q0013001500024Q000900133Q00062Q000A00C30001000400049E3Q00C3000100122Q001300183Q00203E0013001300192Q00FD001400044Q00F00013000200022Q00FD000A00133Q000618000B00CA0001000500049E3Q00CA000100122Q001300183Q00203E0013001300192Q00FD001400054Q00F00013000200022Q00FD000B00133Q001209010300113Q00049E3Q00120001000E0C2Q0100F00001000100049E3Q00F0000100122Q000300263Q00203E0003000300272Q00FD000400014Q00F000030002000200066D000300F000013Q00049E3Q00F000012Q000F010300025Q000103000200032Q000F010400033Q00066A000300F00001000400049E3Q00F000012Q000F010300064Q000F010400074Q00F000030002000200261D000300E40001002800049E3Q00E400012Q000F010300064Q000F010400074Q00F00003000200022Q000F010400033Q00066A000300F00001000400049E3Q00F000012Q000F010300084Q000F010400094Q00F000030002000200261D000300EF0001002800049E3Q00EF00012Q000F010300084Q000F010400094Q00F00003000200022Q000F010400033Q00066A000300F00001000400049E3Q00F000012Q007E000100023Q001209010300014Q007E000300024Q003F3Q00017Q00083Q00028Q00027Q004003063Q0048724461746103073Q005370652Q6C494400026Q00F03F030C3Q004379636C655370652Q6C494403073Q004379636C654D4F00323Q001209012Q00014Q003Q0100023Q000EF30002000900013Q00049E3Q000900012Q000F01036Q00FD000400014Q00F00003000200022Q00FD000200034Q007E000200023Q0026B53Q001A0001000100049E3Q001A00010012092Q0100014Q000F010300013Q00203E00030003000300203E00030003000400261D000300190001000500049E3Q001900012Q000F010300013Q00203E00030003000300203E000300030004000E0C2Q0100190001000300049E3Q001900012Q000F010300013Q00203E00030003000300203E000100030004001209012Q00063Q000EF30006000200013Q00049E3Q000200012Q000F010300013Q00203E00030003000300203E00030003000700261D0003002E0001000500049E3Q002E00012Q000F010300013Q00203E00030003000300203E00030003000800261D0003002E0001000500049E3Q002E00012Q000F010300013Q00203E00030003000300203E000300030007000E0C2Q01002E0001000300049E3Q002E00012Q000F010300013Q00203E00030003000300203E000100030007001209010200013Q001209012Q00023Q00049E3Q000200012Q003F3Q00017Q00093Q00028Q00026Q00F03F03053Q00436F6E524F03053Q005370652Q6C027Q0040026Q001C4003053Q00466C61677303053Q0070616972732Q0100343Q001209012Q00014Q003Q0100023Q000EF30002001300013Q00049E3Q0013000100122Q000300033Q00066D0003001100013Q00049E3Q0011000100122Q000300033Q00203E00030003000400066D0003001100013Q00049E3Q0011000100122Q000300033Q00203E000300030004000E0C2Q0100110001000300049E3Q0011000100122Q000300033Q00203E000100030004001209010200013Q001209012Q00053Q0026B53Q002B0001000100049E3Q002B00010012092Q0100063Q00122Q000300033Q00066D0003002A00013Q00049E3Q002A000100122Q000300033Q00203E00030003000700066D0003002A00013Q00049E3Q002A000100122Q000300083Q00122Q000400033Q00203E0004000400072Q002500030002000500049E3Q002800010026B5000700280001000900049E3Q0028000100261D000600280001000100049E3Q002800012Q00FD000100063Q00049E3Q002A0001000663000300220001000200049E3Q00220001001209012Q00023Q0026B53Q00020001000500049E3Q000200012Q000F01036Q0017000400016Q0003000200024Q000200036Q000200023Q00044Q000200012Q003F3Q00017Q00083Q00028Q0003063Q004D617844707303053Q00466C61677303053Q0070616972732Q01026Q00F03F027Q004003053Q005370652Q6C00363Q001209012Q00014Q003Q0100023Q0026B53Q001A0001000100049E3Q001A00010012092Q0100013Q00122Q000300023Q00066D0003001900013Q00049E3Q0019000100122Q000300023Q00203E00030003000300066D0003001900013Q00049E3Q0019000100122Q000300043Q00122Q000400023Q00203E0004000400032Q002500030002000500049E3Q001700010026B5000700170001000500049E3Q0017000100261D000600170001000100049E3Q001700012Q00FD000100063Q00049E3Q00190001000663000300110001000200049E3Q00110001001209012Q00063Q0026B53Q00210001000700049E3Q002100012Q000F01036Q00FD000400014Q00F00003000200022Q00FD000200034Q007E000200023Q0026B53Q00020001000600049E3Q0002000100122Q000300023Q00066D0003003200013Q00049E3Q0032000100122Q000300023Q00203E00030003000800066D0003003200013Q00049E3Q0032000100122Q000300023Q00203E000300030008000E0C2Q0100320001000300049E3Q003200010026B5000100320001000100049E3Q0032000100122Q000300023Q00203E000100030008001209010200013Q001209012Q00073Q00049E3Q000200012Q003F3Q00017Q00",
    GetFEnv(), ...);
