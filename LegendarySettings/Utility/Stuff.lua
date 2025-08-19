-- Last Update: 08/01/2025
-- Author: Kaneto & Gojira
-- Addon
local name, LS = ...
-- LegendarySettings
local LS = LegendarySettings;

LS.BigWigsData = {
    Messages = 0,
    Sounds = 0
}

LS.HrData = {
    CastText = "",
    CycleSpellID = 0,
    CycleMO = false,
    CycleUnit = false,
    Token = nil,
    NotInRange = false,
    SpellID = 0,
    TargetInMelee = 0,
    TargetInRange = 0,
    TargetInSplash = 0
}

LS.GlobalData = {
    SpellID = 0,
    Cycle = false,
    CooldownToggle = false,
    FightRemains = 0,
    EnemiesInMelee = 0,
    EnemiesInRange = 0,
    RangeToTarget = 0,
    RotationHelper = ""
}

-- Reset the table when the player leaves combat
local combatFrame = CreateFrame("Frame")
combatFrame:RegisterEvent("PLAYER_REGEN_ENABLED")
combatFrame:RegisterEvent("PLAYER_REGEN_DISABLED")

combatFrame:SetScript("OnEvent", function(self, event)
    if event == "PLAYER_REGEN_ENABLED" then
        LS.BigWigsData.Messages = 0
        LS.BigWigsData.Sounds = 0
    end
end)

-- Hook to get BigWigs messages and sounds
local function BigWigsHook()
    -- Check if BigWigs is loaded
    local loadingBW, finishedBW = C_AddOns.IsAddOnLoaded("BigWigs_Core")
    -- Create a table to store messages and sounds
    local bigWigsLogs = {
        messages = {}
    }
    if loadingBW and finishedBW then
        if not LS._BigWigsHooked then
            -- Hook into the SendMessage function using hooksecurefunc
            hooksecurefunc(BigWigsLoader, "SendMessage", function(self, event, ...)
                if event == "BigWigs_Message" then
                    local module, key, text, color = ...
                    table.insert(bigWigsLogs.messages, {
                        timestamp = GetTime(),
                        text = text,
                        color = color
                    })
                end
                local lastMessage = bigWigsLogs.messages[#bigWigsLogs.messages]
                if lastMessage and (GetTime() - lastMessage.timestamp) <= 4 then
                    local isTanking, status = UnitDetailedThreatSituation("player", "target")
                    -- Use Healing CDs
                    if lastMessage.color == "orange" then
                        LS.BigWigsData.Messages = 1
                        -- Messages which require Defensives as a tank
                    elseif (lastMessage.color == "purple" or lastMessage.color == "blue") and isTanking then
                        LS.BigWigsData.Messages = 2
                    end
                end
            end)
            LS._BigWigsHooked = true
        end
    end
end

-- Hook to get WeakAura sounds
local function WeakAuraHook()
    -- Check if WeakAuras is loaded
    local loadingWA, finishedWA = C_AddOns.IsAddOnLoaded("WeakAuras")
    local weakAuraLogs = {
        messages = {},
        sounds = {}
    }
    if loadingWA and finishedWA then
        -- HOOK the PlaySound function just once (only if not already hooked).
        -- This will let us capture the local 'Sound' each time WA.PlaySound is called.
        if not LS._WeakAuraHooked then
            hooksecurefunc("PlaySoundFile", function(Sound, ...)
                table.insert(weakAuraLogs.sounds, {
                    timestamp = GetTime(),
                    sound = Sound
                })
                local lastSound = weakAuraLogs.sounds[#weakAuraLogs.sounds]
                local isTanking, status = UnitDetailedThreatSituation("player", "target")
                if lastSound and (GetTime() - lastSound.timestamp) <= 4 then
                    -- Use Self Defensives
                    if lastSound.sound == "[ZTV] AoE" or lastSound.sound == "[ZTV] Targeted" or lastSound.sound == "AoE" or
                        lastSound.sound == "Targeted" or lastSound.sound == "Big Wigs: Alarm" then
                        LS.BigWigsData.Sounds = 1
                        -- Tank Swap
                    elseif lastSound.sound == "Big Wigs: Warning" or lastSound.sound == "Big Wigs: Alarm" or
                        lastSound.sound == "[ZTV] Taunt" or lastSound.sound == "Taunt" or lastSound.sound ==
                        "Acoustic Guitar" and (not isTanking or status <= 1) then
                        LS.BigWigsData.Sounds = 2
                        -- Use Healing CDs
                    elseif lastSound.sound == "[ZTV] AoE" or lastSound.sound == "AoE" then
                        LS.BigWigsData.Messages = 1
                        -- Use CC
                    elseif lastSound.sound == "[ZTV] CC" or lastSound.sound == "CC" then
                        LS.BigWigsData.Sounds = 3
                        -- Use Kick
                    elseif lastSound.sound == "[ZTV] Kick" or lastSound.sound == "Kick" then
                        LS.BigWigsData.Sounds = 4
                    end
                end
            end)
            LS._WeakAuraHooked = true
        end
    end
end

-- Hook to get the Unit ID token when a nameplate function is called up
local function SetupHeroRotationHook()
    local loading, finished = C_AddOns.IsAddOnLoaded("HeroRotation")
    if loading and finished then
        local HR = HeroRotation
        -- HOOK the AddIcon function just once (only if not already hooked).
        -- This will let us capture the local 'Token' each time HR.Nameplate.AddIcon is called.
        if not LS._MyLegendaryHooked then
            hooksecurefunc(HR.Nameplate, "AddIcon", function(ThisUnit, Object)
                if ThisUnit and ThisUnit.UnitID then
                    LS.HrData.Token = string.lower(ThisUnit.UnitID)
                else
                    LS.HrData.Token = nil
                end
            end)
            LS._MyLegendaryHooked = true
        end
    end
end

-- Hook to get the text of Cast Annotated for Empowered Stage for example
local function CastAnnotatedHook()
    -- Check if HeroRotation is loaded
    local loadingHR, finishedHR = C_AddOns.IsAddOnLoaded("HeroRotation")
    if loadingHR and finishedHR then
        -- Save the original HR.Cast function
        local HR = HeroRotation
        -- HOOK the CastAnnotated function just once (only if not already hooked).
        -- This will let us capture the local 'Text' each time HR.CastAnnotated is called.
        if not LS._TextHooked then
            hooksecurefunc(HR, "CastAnnotated", function(Object, OffGCD, Text, OutofRange, FontSize)
                LS.HrData.CastText = Text
            end)
            LS._TextHooked = true
        end
    end
end

-- Dispel Check
_G.LDispelCacheL = _G.LDispelCacheL or {}
local DispelAfter = LegendarySettings.Settings["dispelAfter"]

-- Initialize group size based on group members
local GroupSize = 0
local members = GetNumGroupMembers()
if members == 0 then
    GroupSize = 1
else
    GroupSize = members
end
if GroupSize > 25 then
    GroupSize = 25
end

-- Convert list to a Lua table for efficient lookups
local DontDispel = {
    [320788] = true, [320790] = true, [323730] = true, [357298] = true, [397385] = true, [334496] = true, [344663] = true, [30113] = true, [328531] = true, [328662] = true, [224563] = true, [330700] = true, [353930] = true, [351117] = true, [350541] = true, [154442] = true, [347283] = true, [366893] = true, [365216] = true, [365294] = true, [322232] = true, [243237] = true, [240443] = true, [227404] = true, [229159] = true, [374352] = true, [377510] = true, [406543] = true, [389179] = true, [278008] = true, [424581] = true, [404141] = true, [405696] = true, [405478] = true, [415769] = true, [415554] = true, [413219] = true, [413315] = true, [425153] = true, [417807] = true, [438677] = true, [446349] = true, [461487] = true, [461492] = true, [461501] = true, [461504] = true, [461507] = true, [461950] = true, [429493] = true, [473690] = true, [473713] = true
}

local dummies = {
    ["NONE"] = true, ["Boulderfist"] = true, ["Animated Duelist"] = true, ["Dungeoneer's Training Dummy"] = true, ["Raider's Training Dummy"] = true, ["Training Dummy"] = true, ["Black Dragon's Challenge Dummy"] = true, ["Cleave Training Dummy"] = true, ["Normal Tank Dummy"] = true, ["PvP Training Dummy"] = true, ["Undercity Practice Dummy"] = true, ["Raider's Tanking Dummy"] = true, ["Dungeoneer's Tanking Dummy"] = true, ["Swarm Training Dummy"] = true, ["Normal Healing Dummy"] = true, ["Dungeon Tank Dummy"] = true, ["Killable Damage Dummy"] = true, ["Target Dummy"] = true, ["Initiate's Training Dummy"] = true, ["Dungeon Damage Dummy"] = true, ["Boxer's Training Dummy"] = true, ["Prepfoot Training Dummy"] = true, ["Veteran's Training Dummy"] = true, ["Disciple's Training Dummy"] = true, ["Ebon Knight's Training Dummy"] = true, ["Theramore Combat Dummy"] = true, ["Mortar Team Advanced Target Dummy"] = true, ["Gnoll Target Dummy"] = true, ["Ub3r-Improved Target Dummy"] = true, ["Combat Dummy"] = true, ["Advanced Target Dummy"] = true, ["Anatomical Dummy"] = true, ["Doug Test - Healing Dummy"] = true, ["Combat Test Dummy 112"] = true, ["Combat Test Dummy 88"] = true, ["Combat Test Dummy 92"] = true, ["Combat Test Dummy 93"] = true, ["Theramore Combat Dummy 4"] = true, ["Combat Test Dummy 102"] = true, ["Combat Test Dummy 113"] = true, ["Gizlock's Dummy"] = true, ["Impact Test Dummy - Giant"] = true, ["Mythic Damage Dummy"] = true, ["Normal Damage Dummy"] = true, ["Combat Test Dummy 100 (Legion)"] = true, ["Combat Test Dummy 103"] = true, ["Combat Test Dummy 110"] = true, ["Combat Test Dummy 120 No Armor"] = true, ["Combat Test Dummy 60 No Armor"] = true, ["Combat Test Dummy 60 Root Spam"] = true, ["Combat Test Dummy 60 Spell Catch and Release"] = true, ["Combat Test Dummy 85"] = true, ["Combat Test Dummy 87"] = true, ["Combat Test Dummy 90"] = true, ["Group Healing Dummy"] = true, ["High HP Healing Test Dummy 113"] = true, ["High HP Killable Combat Test Dummy 113"] = true, ["Impact Test Dummy - Black"] = true, ["Impact Test Dummy - Blue"] = true, ["Impact Test Dummy - Green"] = true, ["Impact Test Dummy - Kodo"] = true, ["Impact Test Dummy - Ogre"] = true, ["Impact Test Dummy - Red"] = true, ["Impact Test Dummy - Shadow"] = true, ["Impact Test Dummy - Vrykul"] = true, ["Larry Test Combat Dummy - Faction 1194"] = true, ["Larry Test Combat Dummy - Faction 7"] = true, ["Minor Damage Dummy"] = true, ["Naxxramas Combat Dummy"] = true, ["Practice Dummy"] = true, ["Raid Damage Dummy"] = true, ["Raid Tank Dummy"] = true, ["Raptor Target Dummy"] = true, ["Testing Dummy"] = true, ["Testing Tech Tree Dummy"] = true, ["Timed Damage Dummy"] = true, ["Unarmored Damage Dummy"] = true, ["Visual Test Dummy Large"] = true, ["Visual Test Dummy Medium"] = true, ["Visual Test Dummy Small"] = true, ["Warug's Target Dummy"] = true, ["Weak Damage Dummy"] = true, ["Weak Tank Dummy"] = true, ["[DNT] Combat Test Dummy 100"] = true, ["DPS Survivability Dummy"] = true, ["Crystalmaw"] = true, ["Kelpfist"] = true
}
-- Initialize debuff types
local Magic, Disease, Poison, Curse = 'NONE', 'NONE', 'NONE', 'NONE'

-- Get player class and specialization information
local localizedClass, englishClass, classIndex = UnitClass('player')
local currentSpec = GetSpecialization()
local id, specName, description, icon, background, role = GetSpecializationInfo(currentSpec)

-- Determine the types of debuffs based on the player’s class and spec
if specName and englishClass then
    local unitGetSpec = string.upper(englishClass .. ':' .. specName)

    if unitGetSpec == 'DRUID:RESTORATION' or unitGetSpec == 'SHAMAN:RESTORATION' or unitGetSpec == 'PRIEST:HOLY' or
        unitGetSpec == 'PRIEST:DISCIPLINE' or unitGetSpec == 'MONK:MISTWEAVER' or unitGetSpec == 'EVOKER:PRESERVATION' or
        unitGetSpec == 'PALADIN:HOLY' then
        Magic = 'Magic'
    end

    if Magic == 'NONE' and role == 'HEALER' then
        Magic = 'Magic'
    end

    -- Healers
    if IsPlayerSpell(392378) then -- Improved Nature's Cure
        Curse, Poison = 'Curse', 'Poison'
    end
    if IsPlayerSpell(2782) then -- Remove Corruption
        Curse = 'Curse'
    end

    -- Paladin & Monk
    if IsPlayerSpell(388874) or IsPlayerSpell(393024) then -- Improved Detox & Improved Cleanse
        Poison, Disease = 'Poison', 'Disease'
    end
    if IsPlayerSpell(218164) or IsPlayerSpell(213644) then -- Detox & Cleanse Toxins
        Disease, Poison = 'Disease', 'Poison'
    end

    -- Shaman
    if IsPlayerSpell(383016) or IsPlayerSpell(51886) then -- Improved Purify Spirit & Cleanse Spirit
        Curse = 'Curse'
    end

    -- Priest
    if IsPlayerSpell(390632) or IsPlayerSpell(213634) then -- Improved Purify & Purify Disease
        Disease = 'Disease'
    end

    -- Evoker
    if IsPlayerSpell(360823) or IsPlayerSpell(365585) then -- Naturalize & Expunge
        Poison = 'Poison'
    end

    -- Other Than Healers
    if IsPlayerSpell(205604) then -- Reverse Magic (DH PVP)
        Magic = 'Magic'
    end

    if IsPlayerSpell(212640) then -- Mending Bandage (Survival Hunter PVP)
        Poison, Disease = 'Poison', 'Disease'
    end

    if IsPlayerSpell(475) then -- Remove Curse (Mage)
        Curse = 'Curse'
    end

    if IsPlayerSpell(89808) then -- Singe Magic (Warlock)
        Magic = 'Magic'
    end
end

-- Function to get unit health percentage
local function GetUnitHealth(unit)
    local exists = UnitExists(unit)
    if exists then
        local health = UnitHealth(unit) or 0
        local maxHealth = UnitHealthMax(unit) or 1
        return health / maxHealth
    end
    return 0
end
-- Table to store unit health values
local groupDispelUnitHealths = {}

-- Check for units in the group
for UnitN = 0, GroupSize - 1 do
    local unit = (UnitN == 0) and 'player' or (GroupSize <= 5) and 'party' .. UnitN or 'raid' .. UnitN

    AuraUtil.ForEachAura(unit, 'HARMFUL|RAID', nil,
        function(name, _, _, dispelType, duration, expirationTime, _, _, _, spellid, ...)
            if (not DontDispel[spellid]) and dispelType and
                (dispelType == Magic or dispelType == Poison or dispelType == Disease or dispelType == Curse) or spellid ==
                440313 then
                local timeLeft = expirationTime - GetTime()
                if timeLeft <= (duration - DispelAfter) then -- Check if the debuff has been on the unit for at least DispelAfter seconds
                    local unitHealth = GetUnitHealth(unit)
                    if unitHealth > 0 and (UnitInRange(unit) or unit == 'player') then
                        table.insert(groupDispelUnitHealths, {
                            unit = unit,
                            health = unitHealth
                        })
                    end
                end
            end
        end)
end
-- Sort the unitHealths table based on health in ascending order
table.sort(groupDispelUnitHealths, function(a, b)
    return a.health < b.health
end)
-- Determine the unit to dispel
local groupUnitToDispel
if #groupDispelUnitHealths > 0 then
    if UnitGroupRolesAssigned(groupDispelUnitHealths[1].unit) == 'TANK' and #groupDispelUnitHealths == 1 then
        groupUnitToDispel = groupDispelUnitHealths[1].unit
    elseif UnitGroupRolesAssigned(groupDispelUnitHealths[1].unit) ~= 'TANK' then
        groupUnitToDispel = groupDispelUnitHealths[1].unit
    elseif #groupDispelUnitHealths > 1 then
        groupUnitToDispel = groupDispelUnitHealths[2].unit
    end
end
-- Calculate y value for dispel target
local y = 0
if groupUnitToDispel then
    if groupUnitToDispel == 'player' then
        y = 100
    else
        local unitNumber = tonumber(string.match(groupUnitToDispel, '%d+'))
        if unitNumber then
            if string.find(groupUnitToDispel, 'raid') then
                y = unitNumber
            else
                y = unitNumber
            end
        end
    end
end

local function ShouldDispelCustom(unit, returnValue)
    local Name = UnitName(unit)
    if Name ~= nil then
        if not dummies[Name] then
            local IsFriend = UnitIsFriend('player', unit)
            if IsFriend ~= nil and IsFriend == true then
                AuraUtil.ForEachAura(unit, 'HARMFUL|RAID', nil,
                    function(name, _, _, dispelType, _, _, _, _, _, spellid, ...)
                        if dispelType and
                            (dispelType == Magic or dispelType == Poison or dispelType == Disease or dispelType == Curse) then
                            return returnValue
                        end
                    end)
            end
        end
    end

    return 0
end
local customDispelUnit = 0
local customDispelUnits = {'mouseover', 'target'}
for _, unit in ipairs(customDispelUnits) do
    if unit == 'target' then
        if customDispelUnit == 0 then
            customDispelUnit = ShouldDispelCustom('target', 300)
        end
    elseif unit == 'mouseover' then
        if customDispelUnit == 0 then
            customDispelUnit = ShouldDispelCustom('mouseover', 200)
        end
    end
end
_G.LDispelCacheL = {
    groupUnit = y,
    customUnit = customDispelUnit
}

-- Initialize cache and frame
_G.nameplateLUnitsCache = _G.nameplateLUnitsCache or {}
_G.nameplateLUnitsCacheFrame = _G.nameplateLUnitsCacheFrame or CreateFrame("FRAME")

-- Event handling and initialization
if not _G.nameplateLUnitsCacheFrame.initialized then
    _G.nameplateLUnitsCacheFrame:RegisterEvent("PLAYER_ENTERING_WORLD")
    _G.nameplateLUnitsCacheFrame:RegisterEvent("NAME_PLATE_UNIT_ADDED")
    _G.nameplateLUnitsCacheFrame:RegisterEvent("NAME_PLATE_UNIT_REMOVED")
    _G.nameplateLUnitsCacheFrame:RegisterEvent("LOADING_SCREEN_DISABLED")

    _G.nameplateLUnitsCacheFrame:SetScript("OnEvent", function(self, event, unitToken, ...)
        if event == "PLAYER_ENTERING_WORLD" or event == 'LOADING_SCREEN_DISABLED' then
            _G.nameplateLUnitsCache = {} -- Clear the cache on entering a new instance
        elseif event == "NAME_PLATE_UNIT_ADDED" then
            if unitToken then
                HandleLNameplateUnitsCacheAdded(unitToken)
            end
        elseif event == "NAME_PLATE_UNIT_REMOVED" then
            if unitToken then
                HandleLNameplateUnitsCacheRemoved(unitToken)
            end
        end
    end)

    _G.nameplateLUnitsCacheFrame.initialized = true
end

-- Functions to handle nameplate events (defined within the frame's scope)
function HandleLNameplateUnitsCacheAdded(unitToken)
    local unitPlate = C_NamePlate.GetNamePlateForUnit(unitToken, true)
    if unitPlate then
        local unitPlateToken = unitPlate.namePlateUnitToken
        local unitName = UnitName(unitPlateToken)
        local unitGuid = UnitGUID(unitPlateToken)
        local unitType, _, _, _, _, npc_id, _ = strsplit('-', unitGuid)

        if unitType ~= "GameObject" or unitType ~= "Vehicle" then
            _G.nameplateLUnitsCache[unitPlateToken] = {
                unitPlate = unitPlateToken,
                unitName = unitName,
                unitGUID = unitGuid,
                unitId = npc_id
            }
        end
    end
end

function HandleLNameplateUnitsCacheRemoved(unitToken)
    if _G.nameplateLUnitsCache[unitToken] ~= nil then
        _G.nameplateLUnitsCache[unitToken] = nil
    end
end

-- Range and Enemies Check
_G.LRangeCheckL = _G.LRangeCheckL or {}
local itemRanges = {
    ["item:16114"] = 4,
    ["item:37727"] = 5,
    ["item:15826"] = 5,
    ["item:63427"] = 5,
    ["item:34368"] = 7,
    ["item:32321"] = 7,
    ["item:17626"] = 7,
    ["item:33069"] = 15,
    ["item:10645"] = 20,
    ["item:24268"] = 25,
    ["item:835"] = 30,
    ["item:9328"] = 30,
    ["item:24269"] = 35,
    ["item:1399"] = 35,
    ["item:28767"] = 40,
    ["item:4945"] = 40,
    ["item:32698"] = 45,
    ["item:116139"] = 50,
    ["item:32825"] = 60,
    ["item:41265"] = 70,
    ["item:35278"] = 80,
    ["item:33119"] = 100
}

local function RangeCheck(unit)
    local currentRange = 100

    for item, range in pairs(itemRanges) do
        if C_Item.IsItemInRange(item, unit) and range < currentRange then
            currentRange = range
        end
    end

    local autoShootname = nil
    local isSpellInRange = nil
    local IsRetail = true
    if IsRetail then
        autoShootname = C_Spell.GetSpellInfo(75)
        isSpellInRange = autoShootname.name ~= nil and C_Spell.IsSpellInRange(autoShootname.name, unit)
    else
        local name, rank, icon, castTime, minRange, maxRange, spellID, originalIcon = GetSpellInfo(spell)
        autoShootname = {
            name = name,
            rank = rank,
            icon = icon,
            castTime = castTime,
            minRange = minRange,
            maxRange = maxRange,
            spellID = spellID,
            originalIcon = originalIcon
        }
        isSpellInRange = (autoShootname.name ~= nil and IsSpellInRange(autoShootname.name, unit) == 1) and true or false
    end

    if currentRange < 8 and isSpellInRange == true then
        currentRange = 8
    end

    return currentRange
end

local ForceIds = {} -- Initialize or populate this table as needed
local MeleeCount, RangedCount = 0, 0
local nameplates = _G.nameplateLUnitsCache or {}

if nameplates then
    for _, unitData in pairs(nameplates) do
        local unitPlate = unitData.unitPlate

        if unitPlate then
            local forceInC = ForceIds[tonumber(unitData.unitId)] == true
            local inCombat = (UnitAffectingCombat(unitPlate) and UnitReaction('player', unitPlate) and
                                 UnitReaction('player', unitPlate) <= 4) or forceInC
            local unitIsTargetingGroup = UnitInParty('targettarget') or UnitInRaid('targettarget') or
                                             UnitIsUnit('targettarget', 'player')
            local rangeCheck = (inCombat and RangeCheck(unitPlate))

            if unitPlate and inCombat then
                if unitIsTargetingGroup or rangeCheck <= 8 or forceInC then
                    MeleeCount = MeleeCount + 1
                end
                if unitIsTargetingGroup or rangeCheck <= 40 or forceInC then
                    RangedCount = RangedCount + 1
                end
            end
        end
    end
end

local TargetRange = 100
if UnitReaction('player', 'target') and UnitReaction('player', 'target') <= 4 then
    local targetRangeCheck = RangeCheck('target')
    if targetRangeCheck then
        TargetRange = targetRangeCheck
    end
end

if _G.LRangeCheckL then
    _G.LRangeCheckL.UnitsInMelee = MeleeCount
    _G.LRangeCheckL.UnitsInRange = RangedCount
    _G.LRangeCheckL.Target = TargetRange
end

-- Interrupt Stuff
_G.InterruptLFrameCache = _G.InterruptLFrameCache or CreateFrame('FRAME')
_G.InterruptLUnitsCache = _G.InterruptLUnitsCache or {}
_G.KickSpellIds = _G.KickSpellIds or {}
local kickEverything = not LegendarySettings.Settings["interruptOnlyWhitelist"]

if not _G.InterruptLFrameCache.initialized then
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_CHANNEL_START')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_CHANNEL_STOP')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_CHANNEL_UPDATE')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_EMPOWER_START')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_EMPOWER_STOP')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_EMPOWER_UPDATE')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_START')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_STOP')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_INTERRUPTED')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_SUCCEEDED')
    _G.InterruptLFrameCache:RegisterEvent('UNIT_SPELLCAST_NOT_INTERRUPTIBLE')

    _G.InterruptLFrameCache:SetScript('OnEvent', function(self, event, unitTarget, castGUID, spellID, complete, ...)
        if event == 'UNIT_SPELLCAST_CHANNEL_STOP' or event == 'UNIT_SPELLCAST_STOP' or event ==
            'UNIT_SPELLCAST_EMPOWER_STOP' or event == 'UNIT_SPELLCAST_INTERRUPTED' or event ==
            'UNIT_SPELLCAST_SUCCEEDED' then
            _G.InterruptLUnitsCache[unitTarget] = nil
        elseif string.match(unitTarget, 'nameplate') then
            local type

            if event == 'UNIT_SPELLCAST_CHANNEL_START' or event == 'UNIT_SPELLCAST_CHANNEL_UPDATE' or event ==
                'UNIT_SPELLCAST_EMPOWER_START' or event == 'UNIT_SPELLCAST_EMPOWER_UPDATE' then
                type = 'CHANNEL'
            elseif event == 'UNIT_SPELLCAST_START' then
                type = 'CAST'
            end

            -- Check if the spell should be interrupted
            local kick = _G.KickSpellIds[spellID] or kickEverything

            if kick then
                -- Determine if the spell is interruptable
                local isInterruptable = false
                if type == 'CHANNEL' then
                    local name, displayName, textureID, startTimeMs, endTimeMs, isTradeskill, notInterruptible, spellID,
                        isEmpowered, numEmpowerStages = UnitChannelInfo(unitTarget)
                    isInterruptable = notInterruptible == false and UnitReaction('player', unitTarget) <= 4
                elseif type == 'CAST' then
                    local name, text, texture, startTimeMS, endTimeMS, isTradeSkill, castID, notInterruptible, spellId =
                        UnitCastingInfo(unitTarget)

                    isInterruptable = notInterruptible == false and UnitReaction('player', unitTarget) <= 4
                end

                -- Update cache with the unit data if conditions are met
                if isInterruptable then
                    _G.InterruptLUnitsCache[unitTarget] = {
                        spellId = spellID,
                        target = unitTarget,
                        interruptType = type
                    }
                end
            end
        end
    end)

    _G.InterruptLFrameCache.initialized = true
end

-- Create a frame for our OnUpdate script
local updateFrame = CreateFrame("Frame", "MyLegendaryUpdateFrame", UIParent)

-- Now our OnUpdate handler
updateFrame:SetScript("OnUpdate", function(self, elapsed)
    -- Attempt to hook if not already
    SetupHeroRotationHook()
    CastAnnotatedHook()
    BigWigsHook()
    WeakAuraHook()

    -- Check if HeroRotation is loaded
    local loadingHR, finishedHR = C_AddOns.IsAddOnLoaded("HeroRotation")

    if loadingHR and finishedHR then
        local HR = HeroRotation
        local HL = HeroLib

        local EnemiesMelee = HL.Unit.Player:GetEnemiesInMeleeRange(10)
        local EnemiesRange = HL.Unit.Player:GetEnemiesInRange(40)
        local Enemies10ySplash = HL.Unit.Target:GetEnemiesInSplashRange(10)
        if #EnemiesMelee > 0 then
            LS.HrData.TargetInMelee = #EnemiesMelee
        end
        if #EnemiesRange > 0 then
            LS.HrData.TargetInRange = #EnemiesRange
        end
        if #Enemies10ySplash > 0 then
            LS.HrData.TargetInSplash = #Enemies10ySplash
        end

        -- If the LeftIconFrame exists and is visible, do our logic
        if HR.LeftIconFrame and HR.LeftIconFrame:IsVisible() then
            LS.HrData.CycleSpellID = HR.LeftIconFrame.ID
            -- 'Token' was saved into LS.HrData.Token by our hook
            local token = LS.HrData.Token
            if token then
                local nameplate = C_NamePlate.GetNamePlateForUnit(token)
                if nameplate and nameplate.namePlateUnitGUID then
                    local nameplateUUID = nameplate.namePlateUnitGUID

                    if UnitGUID("mouseover") == nameplateUUID then
                        LS.HrData.CycleMO = true
                        LS.HrData.CycleUnit = false
                    else
                        LS.HrData.CycleMO = false
                        LS.HrData.CycleUnit = true
                    end
                else
                    -- If there's no valid nameplate for that token,
                    -- we could reset or do some fallback
                    LS.HrData.CycleMO = false
                    LS.HrData.CycleUnit = false
                end
            else
                -- We don't have a Token yet
                LS.HrData.CycleMO = false
                LS.HrData.CycleUnit = false
            end
        else
            -- LeftIconFrame not visible; reset CycleSpellID
            LS.HrData.CycleSpellID = 0
            LS.HrData.CycleMO = false
            LS.HrData.CycleUnit = false
        end

        if HR.MainIconFrame and HR.MainIconFrame:IsVisible() then
            -- Do something with HR.MainIconFrame.ID
            local r, g, b = HR.MainIconFrame.Texture:GetVertexColor()
            if g < 1 and g > 0.4 and b < 1 then
                LS.HrData.NotInRange = true
            else
                LS.HrData.NotInRange = false
            end

            if HR.MainIconFrame.ID and not LS.HrData.NotInRange then
                LS.HrData.SpellID = HR.MainIconFrame.ID
            else
                LS.HrData.SpellID = 0
            end
        else
            LS.HrData.SpellID = 0
            LS.HrData.NotInRange = false
        end
    end

    -- Initialize global caches
    _G.LHekiliRecIdL = _G.LHekiliRecIdL or {}
    _G.LHeroRotationRecIdL = _G.LHeroRotationRecIdL or {}
    _G.LConRORecIdL = _G.LConRORecIdL or {}
    _G.LMaxDPSRecIdL = _G.LMaxDPSRecIdL or {}

    -- Initialize Spell Functions
    local function GetUnitCastFinish(cast_endMS)
        if cast_endMS then
            return cast_endMS - (GetTime() * 1000)
        end
        return nil
    end

    local function GetUnitChannelDuration(endTimeMS)
        if endTimeMS then
            return endTimeMS - (GetTime() * 1000)
        end
        return nil
    end

    local function SpellCooldown(spellID)
        local spellcd = C_Spell.GetSpellCooldown(spellID)

        return spellcd ~= nil and spellcd.startTime ~= nil and (spellcd.duration - (GetTime() - spellcd.startTime)) *
                   1000 or 0
    end

    local function ItemCooldown(spellID)
        local startTime, duration, _ = C_Item.GetItemCooldown(spellID)

        return startTime ~= 0 and (duration - (GetTime() - startTime)) * 1000 or 0
    end

    local gcdTable = C_Spell.GetSpellCooldown(61304)
    local gcdStart = gcdTable.startTime
    local gcdDuration = gcdTable.duration
    local spellQueueWindow = tonumber(GetCVar("SpellQueueWindow"))
    local _, _, _, latencyWorld = GetNetStats()
    local SQW = latencyWorld + spellQueueWindow

    local _, _, _, _, casting_endTimeMS, _, _, _, _ = UnitCastingInfo('player')
    local _, _, _, _, channeling_endTimeMS, _, _, _ = UnitChannelInfo('player')

    -- Getting Hekili Spell IDs
    local loadingHek, finishedHek = C_AddOns.IsAddOnLoaded('Hekili')

    if loadingHek and finishedHek then
        local mode = HekiliDB and HekiliDB.profiles.Default.toggles.mode.value or ''

        local shouldUseDual = false

        if mode == 'reactive' or mode == 'dual' then
            shouldUseDual = true
        end

        local dontCycleSpells = {
            [80240] = true -- Havoc
        }

        local function ShouldCycle(hekiliID)
            for spellID, _ in pairs(dontCycleSpells) do
                if spellID == hekiliID then
                    return false
                end
            end
            return true
        end

        local function GetRecommendedHekiliIDs()
            local recommendations = {
                Primary = Hekili and Hekili.DisplayPool.Primary.Recommendations or {},
                AOE = (Hekili and shouldUseDual) and Hekili.DisplayPool.AOE.Recommendations or {}
            }

            local numIcons = {
                Primary = Hekili and Hekili.DisplayPool.Primary.numIcons or 0,
                AOE = (Hekili and shouldUseDual) and Hekili.DisplayPool.AOE.numIcons or 0
            }

            local results = {
                Primary = 0,
                AOE = 0
            }

            local function processHekiliRecommendation(recommendation)
                local rec
                if recommendation[1] then
                    rec = recommendation[1]
                end
                if rec and rec.actionID then
                    local id = rec.actionID
                    local wait = rec.wait * 1000
                    local cycle = rec.indicator == 'cycle' and Hekili.State.settings.spec.cycle == true and
                                      LegendarySettings.Settings["autoCycle"] == true

                    local moving = IsPlayerMoving()
                    local cd = SpellCooldown(id)

                    if cycle and ShouldCycle(id) then
                        return 10101010
                    elseif id < 0 then
                        local spell = Hekili.Class.abilities[id]
                        if spell and spell.item then
                            if ItemCooldown(spell.item) <= 1 and (cd - gcdDuration) <= SQW then
                                local topTrinketLink = GetInventoryItemLink('player', 13)
                                local bottomTrinketLink = GetInventoryItemLink('player', 14)
                                local weaponLink = GetInventoryItemLink('player', 16)
                                local offHandLink = GetInventoryItemLink('player', 17)
                                local cloakLink = GetInventoryItemLink('player', 15)
                                local glovesLink = GetInventoryItemLink('player', 10)

                                local trinketid = topTrinketLink and C_Item.GetItemInfoInstant(topTrinketLink)
                                local bottomTrinketid = bottomTrinketLink and
                                                            C_Item.GetItemInfoInstant(bottomTrinketLink)
                                local weaponid = weaponLink and C_Item.GetItemInfoInstant(weaponLink)
                                local offhandid = offHandLink and C_Item.GetItemInfoInstant(offHandLink)
                                local cloakid = cloakLink and C_Item.GetItemInfoInstant(cloakLink)
                                local glovesid = glovesLink and C_Item.GetItemInfoInstant(glovesLink)

                                local idToUse

                                if trinketid == spell.item then
                                    idToUse = 1
                                elseif bottomTrinketid == spell.item then
                                    idToUse = 2
                                elseif weaponid == spell.item then
                                    idToUse = 3
                                elseif offhandid == spell.item then
                                    idToUse = 4
                                elseif cloakid == spell.item then
                                    idToUse = 6
                                elseif glovesid == spell.item then
                                    idToUse = 7
                                else
                                    idToUse = spell.item
                                end

                                if idToUse then
                                    return idToUse
                                end
                            end
                        end

                        local usePotion = Hekili.DB.profile.toggles.potions.value
                        if usePotion then
                            local potionName = LS.Settings["DPSPotionName"]
                            local potionCount = C_Item.GetItemCount(potionName)
                            if potionCount > 0 then
                                local potionLink = select(2, C_Item.GetItemInfo(potionName))
                                local potionid = potionLink and C_Item.GetItemInfoInstant(potionLink)
                                if potionid and potionid == math.abs(id) and ItemCooldown(potionid) <= 10 then
                                    return 5
                                end
                            end
                        end
                    elseif id > 0 and C_Spell.IsSpellUsable(id) and (cd - gcdDuration) <= SQW and
                        (GetUnitCastFinish(casting_endTimeMS) == nil or GetUnitCastFinish(casting_endTimeMS) <= SQW) and
                        (GetUnitChannelDuration(channeling_endTimeMS) == nil or
                            GetUnitChannelDuration(channeling_endTimeMS) <= SQW) then
                        return id
                    end

                    return 0
                end
            end

            results.Primary = processHekiliRecommendation(recommendations.Primary)
            if shouldUseDual then
                results.AOE = processHekiliRecommendation(recommendations.AOE)
            end

            return results
        end

        local Hekiliids = GetRecommendedHekiliIDs()
        local HekiliPrimaryID = Hekiliids.Primary
        local HekiliAOEID = Hekiliids.AOE

        if _G.LHekiliRecIdL then
            _G.LHekiliRecIdL.Primary = HekiliPrimaryID
            _G.LHekiliRecIdL.AOE = HekiliAOEID
        end
    else
        if _G.LHekiliRecIdL then
            _G.LHekiliRecIdL.Primary = 0
            _G.LHekiliRecIdL.AOE = 0
        end
    end

    local function processRHrecommendations(spellID)
        if spellID then
            local id = spellID
            local cd = SpellCooldown(id)
            if id > 0 and (ItemCooldown(id) - gcdDuration) <= SQW then
                local topTrinketLink = GetInventoryItemLink('player', 13)
                local bottomTrinketLink = GetInventoryItemLink('player', 14)
                local weaponLink = GetInventoryItemLink('player', 16)
                local offHandLink = GetInventoryItemLink('player', 17)
                local cloakLink = GetInventoryItemLink('player', 15)
                local glovesLink = GetInventoryItemLink('player', 10)

                local trinketid = topTrinketLink and C_Item.GetItemInfoInstant(topTrinketLink)
                local bottomTrinketid = bottomTrinketLink and C_Item.GetItemInfoInstant(bottomTrinketLink)
                local weaponid = weaponLink and C_Item.GetItemInfoInstant(weaponLink)
                local offhandid = offHandLink and C_Item.GetItemInfoInstant(offHandLink)
                local cloakid = cloakLink and C_Item.GetItemInfoInstant(cloakLink)
                local glovesid = glovesLink and C_Item.GetItemInfoInstant(glovesLink)

                local idToUse

                if trinketid == id then
                    idToUse = 1
                elseif bottomTrinketid == id then
                    idToUse = 2
                elseif weaponid == id then
                    idToUse = 3
                elseif offhandid == id then
                    idToUse = 4
                elseif cloakid == id then
                    idToUse = 6
                elseif glovesid == id then
                    idToUse = 7
                end

                if idToUse then
                    return idToUse
                end

                local potionName = LS.Settings["DPSPotionName"]
                local potionCount = C_Item.GetItemCount(potionName)
                if potionCount > 0 then
                    local potionLink = select(2, C_Item.GetItemInfo(potionName))
                    local potionid = potionLink and C_Item.GetItemInfoInstant(potionLink)
                    if potionid and potionid == math.abs(id) and ItemCooldown(potionid) <= 10 then
                        return 5
                    end
                end
            end
            if id > 0 and C_Spell.IsSpellUsable(id) and (cd - gcdDuration) <= SQW and
                (GetUnitCastFinish(casting_endTimeMS) == nil or GetUnitCastFinish(casting_endTimeMS) <= SQW) and
                (GetUnitChannelDuration(channeling_endTimeMS) == nil or GetUnitChannelDuration(channeling_endTimeMS) <=
                    SQW) then
                return id
            end
            return 0
        end
    end

    -- Getting HeroRotation Spell IDs
    if loadingHR and finishedHR then

        local function GetRecommendedHRID()
            local rec = 0
            if LS.HrData.SpellID ~= nil then
                if LS.HrData.SpellID > 0 then
                    rec = LS.HrData.SpellID
                end
            end
            if LS.HrData.CycleSpellID ~= nil and LS.HrData.CycleMO ~= nil then
                if LS.HrData.CycleSpellID > 0 then
                    rec = LS.HrData.CycleSpellID
                end
            end

            local HRresults = 0
            HRresults = processRHrecommendations(rec)
            return HRresults
        end

        local HRids = GetRecommendedHRID()
        local HRPrimaryID = HRids

        if _G.LHeroRotationRecIdL then
            _G.LHeroRotationRecIdL.SpellID = HRPrimaryID
        end
    else
        if _G.LHeroRotationRecIdL then
            _G.LHeroRotationRecIdL.SpellID = 0
        end
    end

    -- Use ConRo to get the Spell ID of the next Spell
    local loadingConRO, finishedConRO = C_AddOns.IsAddOnLoaded("ConRO")
    if loadingConRO and finishedConRO then
        -- Get Spell IDs from ConRO
        local function GetRecommendedConRoID()
            local rec = 07
            -- Check if ConRO and ConRO.Spell or ConRO.Flags are defined
            if ConRO and ConRO.Flags then
                for spellID, flag in pairs(ConRO.Flags) do
                    if flag == true and spellID ~= 0 then
                        rec = spellID
                        break
                    end
                end
            end
            if ConRO and ConRO.Spell and ConRO.Spell > 0 then
                rec = ConRO.Spell
            end
            local CRresults = 0
            CRresults = processRHrecommendations(rec)
            return CRresults
        end

        local CRids = GetRecommendedConRoID()
        local CRPrimaryID = CRids

        if _G.LConRORecIdL then
            _G.LConRORecIdL.SpellID = CRPrimaryID
        end
    end

    -- MaxDPS Spell ID
    local loadingMaxDPS, finishedMaxDPS = C_AddOns.IsAddOnLoaded("MaxDPS")

    if loadingMaxDPS and finishedMaxDPS then
        local function GetRecommendedMaxDPSID()
            local rec = 0
            if MaxDps and MaxDps.Flags then
                for spellID, flag in pairs(MaxDps.Flags) do
                    if flag == true and spellID ~= 0 then
                        rec = spellID
                        break
                    end
                end
            end
            if MaxDps and MaxDps.Spell and MaxDps.Spell > 0 and rec == 0 then
                rec = MaxDps.Spell
            end

            local MDresults = 0
            MDresults = processRHrecommendations(rec)
            return MDresults
        end

        local MDids = GetRecommendedMaxDPSID()
        local MDPrimaryID = MDids

        if _G.LMaxDPSRecIdL then
            _G.LMaxDPSRecIdL.SpellID = MDPrimaryID
        end
    end

    -- Fill Global Data depending on Rotation Helper
    LS.GlobalData.RotationHelper = LegendarySettings.Settings["rotationHelper"] or ""

    if loadingHek and finishedHek and LS.GlobalData.RotationHelper == "Hekili" then
        LS.GlobalData.SpellID = _G.LHekiliRecIdL.Primary
        LS.GlobalData.Cycle = HekiliDisplayPrimary.Recommendations[1].indicator ~= nil and
                                  HekiliDisplayPrimary.Recommendations[1].indicator == 'cycle'
        LS.GlobalData.CooldownToggle = Hekili.State.toggle.cooldowns
        LS.GlobalData.FightRemains = Hekili.State.longest_ttd or 0
        LS.GlobalData.EnemiesInMelee = math.max(_G.LRangeCheckL.UnitsInMelee, Hekili.State.active_enemies)
        LS.GlobalData.EnemiesInRange = math.max(_G.LRangeCheckL.UnitsInRange, Hekili.State.active_enemies)
    elseif loadingHR and finishedHR and LS.GlobalData.RotationHelper == "HeroRotation" then
        LS.GlobalData.SpellID = _G.LHeroRotationRecIdL.SpellID
        LS.GlobalData.Cycle = LegendarySettings.HrData.CycleUnit
        LS.GlobalData.CooldownToggle = HeroRotationCharDB.Toggles[1]
        LS.GlobalData.FightRemains = HeroLib.MaxTimeToDie or 0
        LS.GlobalData.EnemiesInMelee = math.max(_G.LRangeCheckL.UnitsInMelee, LegendarySettings.HrData.TargetInMelee)
        LS.GlobalData.EnemiesInRange = math.max(_G.LRangeCheckL.UnitsInRange, LegendarySettings.HrData.TargetInRange)
    elseif loadingConRO and finishedConRO and LS.GlobalData.RotationHelper == "ConRO" then
        LS.GlobalData.SpellID = _G.LConRORecIdL.SpellID
        LS.GlobalData.Cycle = false
        LS.GlobalData.CooldownToggle = ConRO_BurstButton:IsVisible() or ConRO_FullButton:IsVisible()
        LS.GlobalData.FightRemains = ConRO.GetTimeToDie() or 0
        local MeleeTargets, _ = ConRO:Targets("Melee")
        local RangeTargets, _ = ConRO:Targets("40")
        LS.GlobalData.EnemiesInMelee = math.max(_G.LRangeCheckL.UnitsInMelee, MeleeTargets)
        LS.GlobalData.EnemiesInRange = math.max(_G.LRangeCheckL.UnitsInRange, RangeTargets)
    elseif loadingMaxDPS and finishedMaxDPS and LS.GlobalData.RotationHelper == "MaxDPS" then
        LS.GlobalData.SpellID = _G.LMaxDPSRecIdL.SpellID
        LS.GlobalData.Cycle = false
        LS.GlobalData.CooldownToggle = true
        LS.GlobalData.FightRemains = MaxDps.GetTimeToDie() or 0
        LS.GlobalData.EnemiesInMelee = math.max(_G.LRangeCheckL.UnitsInMelee, MaxDps:SmartAoe())
        LS.GlobalData.EnemiesInRange = math.max(_G.LRangeCheckL.UnitsInRange, MaxDps:SmartAoe())
    else
        LS.GlobalData.SpellID = 0
        LS.GlobalData.Cycle = false
        LS.GlobalData.CooldownToggle = false
        LS.GlobalData.FightRemains = 0
        LS.GlobalData.EnemiesInMelee = _G.LRangeCheckL.UnitsInMelee
        LS.GlobalData.EnemiesInRange = _G.LRangeCheckL.UnitsInRange
    end
    LS.GlobalData.RangeToTarget = RangeCheck('target')
end)
