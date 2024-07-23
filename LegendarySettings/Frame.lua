-- Author      : kaneto
-- Create Date : 9/7/2024

--TODO Restrict/Delay reloading only to out of combat
--TODO Message if spec doesn't match with the settings
--TODO Add a label inside the profiles' "You can have up to 6 profiles"

--TODO Add Header and Tail frames (dark)
--TODO Function to clear/remove the initializedButtons
--TODO Change line numbers to start at one instead of 0
--TODO Add title based on loaded SpecID
--TODO Fix profile Ids and sorting in order

--TODO Change buttons' texture when selected in profiles
--TODO Save last selected minitab
--TODO Mouseover Tooltip for explaining the settings
--TODO Move Profile related functions outside of this lua file

local name, LS = ...

LegendarySettings = LS;

LS.Toggles = {}

LS.Queues = {}

LS.KeysPressed = {}

LS.Buttons = {}
LS.MainButton = {}

LS.ProfileButtons = {}

LS.SettingsFrameTabProfiles = {}
LS.SettingsFrameTabCommands = {}

LS.Tabs = {}

-- /run LegendarySettings.Setup()
-- /run LegendarySettings.AddSlider(2, "Another Slider", 1, 100, 22)
-- /run print(LegendarySettings.Settings["F1"])
-- /run print(LegendarySettingsDB.Profiles["Default2"]["F1"])
-- Label checkbox, label slider, label dropdown, label slider

LS.DebugOn = false;

LS.TabOffsetX = 4;
LS.TabOffsetY = 3;
LS.TabNextOffsetY = 0;

LS.TabBodySizeX = 771;
LS.TabBodySizeY = 446;

LS.TabBodyCategoriesSizeY = 32;

LS.TabButtonSizeX = 120;
LS.TabButtonSizeY = 25;

LS.TabButtonsSpacingX = 4;
LS.TabButtonsSpacingY = 0;

LS.MiniTabOffsetX = 4;
LS.MiniTabOffsetY = 4;
LS.MiniTabNextOffsetX = 0
LS.MiniTabButtonSizeX = 80
LS.MiniTabButtonSizeY = 20;
LS.MiniTabButtonsSpacingX = 2

LS.ControlsSpacingX = 180;

LS.SpacingBetweenLines = 50;
LS.SettingControlHeight = 30;

LS.CheckboxSize = 22;

LS.TextboxSizeX = 130;
LS.TextboxSizeY = 20;

LS.SliderWidth = 130;
LS.SliderHeight = 15;

LS.MaxProfiles = 6;

LS.SpecID = 0;

-- Settings table
LS.Settings = {}
-- /run print(" "..#LegendarySettingsDB.Profiles)
-- /run LegendarySettings.Toggles["AOE"] = not LegendarySettings.Toggles["AOE"]

LS.DefaultSettings = {}

local font = "Interface\\Addons\\LegendarySettings\\Fonts\\BB Condensed.TTF";

local fontAlt = "Interface\\Addons\\LegendarySettings\\Fonts\\PTSansNarrow.TTF";

local fontAltMulti = "Interface\\Addons\\LegendarySettings\\Fonts\\BB Condensed.TTF";

local fontKor = "Interface\\Addons\\LegendarySettings\\Fonts\\BareunBatang 2Medium.ttf";

local normalButtonFont = CreateFont("legendaryFontButtonNormal")
normalButtonFont:SetFont(font, 12, "")
normalButtonFont:SetTextColor(1, 0.725, 0.058, 1.0);
local selectedButtonFont = CreateFont("legendaryFontButtonSelected")
selectedButtonFont:SetFont(font, 12, "")
selectedButtonFont:SetTextColor(0.0, 0.0, 0.0, 1.0);
local normalButtonFontS = CreateFont("legendaryFontButtonNormalS")
normalButtonFontS:SetFont(font, 9, "")
normalButtonFontS:SetTextColor(1, 0.725, 0.058, 1.0);
local selectedButtonFontS = CreateFont("legendaryFontButtonSelectedS")
selectedButtonFontS:SetFont(font, 9, "")
selectedButtonFontS:SetTextColor(0.0, 0.0, 0.0, 1.0);

local normalFont = CreateFont("legendaryFontNormal")
normalFont:SetFont(font, 10, "")
normalFont:SetTextColor(1, 0.725, 0.058, 1.0);

local normalAccentFont = CreateFont("legendaryFontNormalAccent")
normalAccentFont:SetFont(font, 10, "")
normalAccentFont:SetTextColor(1, 0.968, 0.0, 1.0);

local normalAccentFontAlt = CreateFont("legendaryFontNormalAccentAlt")
normalAccentFontAlt:SetFont(fontAlt, 10, "")
normalAccentFontAlt:SetTextColor(1, 0.968, 0.0, 1.0);

local fontAlternativeNormal = CreateFont("legendaryFontAlternativeNormal")
fontAlternativeNormal:SetFont(fontAltMulti, 12, "")
fontAlternativeNormal:SetTextColor(1, 0.725, 0.058, 1.0);

local fontKorNormal = CreateFont("legendaryFontKorNormal")
fontKorNormal:SetFont(fontKor, 10, "")
fontKorNormal:SetTextColor(1, 0.725, 0.058, 1.0);

local fontKorAccent = CreateFont("legendaryFontKorNormalAccent")
fontKorAccent:SetFont(fontKor, 10, "")
fontKorAccent:SetTextColor(1, 0.968, 0.0, 1.0);


-- Profiles
-- Load Settings When addon is loaded
local frame = CreateFrame("FRAME");
frame:RegisterEvent("ADDON_LOADED");
frame:RegisterEvent("PLAYER_LOGOUT");
frame:RegisterEvent("PLAYER_LOGIN");
frame:RegisterEvent("ADDON_ACTION_FORBIDDEN");
frame:RegisterEvent("ADDON_ACTION_BLOCKED");
frame:RegisterEvent("PLAYER_REGEN_DISABLED");
frame:RegisterEvent("PLAYER_REGEN_ENABLED");

local function HandleCommands(msg, editbox)
	if LS.Toggles[string.lower(msg)] ~= nil then
		  if LS.Toggles[string.lower(msg)] then
			LS.Toggles[string.lower(msg)] = false
			print(string.lower(msg)..' Off')
			LS.Buttons[string.lower(msg)]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
			LS.Buttons[string.lower(msg)]:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		else
			LS.Toggles[string.lower(msg)] = true
			print(string.lower(msg)..' On')
			LS.Buttons[string.lower(msg)]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")
			LS.Buttons[string.lower(msg)]:SetNormalFontObject(_G["legendaryFontButtonSelected"])
		end
	else
		local a, b, c = strsplit(" ", string.lower(msg), 3)
		if a == "cast" then
			LS.Queues[b..c] = true
			if b == "custom" then
				C_Timer.After(3.5, function() LS.Queues[b..c] = false end)
			else
				C_Timer.After(2.5, function() LS.Queues[b..c] = false end) -- /run print(LegendarySettings.Queues["targetdisarm"])
			end
		elseif a == "resetqueues" then
			LS.Queues = {}
		elseif a == "hide" then
			if SettingsButton:IsVisible() then
				SettingsButton:Hide()
			else
				SettingsButton:Show()
			end
			if HideButton:IsVisible() then
				HideButton:Hide()
			else
				HideButton:Show()
			end
		elseif a == "debug" then
			LS.DebugOn = not LS.DebugOn
		end
	end
end

SLASH_LEGENDARYSTTNGS1, SLASH_LEGENDARYSTTNGS2, SLASH_LEGENDARYSTTNGS3 = '/legendary', '/LEGENDARY', '/Legendary'

SlashCmdList["LEGENDARYSTTNGS"] = HandleCommands   -- add /hiw and /hellow to command list

function frame:OnEvent(event, arg1)
 if event == "ADDON_LOADED" and arg1 == "LegendarySettings" then
	if LegendarySettingsDB == nil then
		LegendarySettingsDB = {}
	end
 elseif event == "PLAYER_LOGIN" then
	local SpecIndex = GetSpecialization()
	local Spec, _  = GetSpecializationInfo(SpecIndex)
	LS.SpecID = Spec

	if LegendarySettingsDB[LS.SpecID] == nil then
		LegendarySettingsDB[LS.SpecID] = {}
		LegendarySettingsDB[LS.SpecID].Profiles = {}
		LegendarySettingsDB[LS.SpecID].Profiles["Default"] = {}
		LegendarySettingsDB[LS.SpecID].Profiles["Default"].ID = 1
		LegendarySettingsDB[LS.SpecID].SelectedProfile = "Default"
	else
		if LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile] == nil then
			LegendarySettingsDB[LS.SpecID].Profiles["Default"] = {}
			LegendarySettingsDB[LS.SpecID].Profiles["Default"].ID = 1
			LegendarySettingsDB[LS.SpecID].SelectedProfile = "Default"
		end
	end

	LS.InitMiniButtons()
	LS.InitProfilesTab()
	LS.UpdateExistingControls()

	if GetCVar("setupLegendarySettingsCVAR") == nil then 
		RegisterCVar("setupLegendarySettingsCVAR", 0 )
	end
	SetCVar("setupLegendarySettingsCVAR", 0)
 elseif event == "PLAYER_LOGOUT" then
		if LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile] then
			for i, v in pairs(LS.Settings) do
				LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile][i] = v
			end
		end
	elseif event == "ADDON_ACTION_FORBIDDEN" or event == "ADDON_ACTION_BLOCKED" then
		print(debugstack())
	elseif event == "PLAYER_REGEN_DISABLED" then
		--print("Entered Combat")
	elseif event == "PLAYER_REGEN_ENABLED" then
		--print("Exited Combat")
	end
end

--frame:EnableKeyboard(true)
--frame:SetPropagateKeyboardInput(true)
--
--function frame:OnKeyUp(event, arg1)
--	if event == 'Z' then
--		print("Key Released"..event)
--		--KeysPressed["Z"] = false
--		frame:SetPropagateKeyboardInput(true)
--	end
--end
--
--function frame:OnKeyDown(event, arg1)
--	if event == 'Z' then
--		LS.KeysPressed["Z"] = GetTime()
--		print("Key Pressed"..event)
--		frame:SetPropagateKeyboardInput(false)
--	end
--end

frame:SetScript("OnEvent", frame.OnEvent);

--frame:SetScript("OnKeyDown", frame.OnKeyDown);
--frame:SetScript("OnKeyUp", frame.OnKeyUp);

--Setup Controls
function LS.Setup()
	LS.InitTabs("First Tab", "Second Tab", "Third Tab", "Fourth", "Fifth", "Sixth", "Etc", "Another One", "And one with a long name")

	LS.InitMiniTabs(1, "Mini Tab 1", "Mini Tab 2")
	LS.InitMiniTabs(2, "Hi", "I'm a tab", "And one long tab to check the length of the letters")

	LS.AddCheckbox(1, 1, 0, "C1", "Checkbox1", false)
	LS.AddSlider(1, 1, 0, "F1", "Fun1 Slider", 5, 25, 11)
	LS.AddSlider(1, 1, 0, "F21","Fun21 Slider", 6, 66, 6)
	LS.AddCheckbox(1, 2, 0, "C14", "Checkbox11", false)
	LS.AddSlider(1, 2, 0, "F15", "Fun144 Slider", 5, 25, 11)
	LS.AddSlider(1, 2, 0, "F216","Fun2155 Slider", 6, 66, 6)
	LS.AddDropdown(1, 2, 1, "SomeDropdown2344", "DropdownTest22", "123", "Some long option, just for testing", "Option2", "123")
	LS.AddDropdown(1, 1, 1, "SomeDropdown23", "DropdownTest22", "123", "Option1", "Option2", "123")
	LS.AddSlider(1, 1, 1, "Fun2", "Fun2 Slider", 5, 25, 11)
	LS.AddTextbox(1, 1, 1, "Var123", "Text", "box")
	LS.AddSlider(1, 1, 2, "Fun3", "Fun3 Slider", 5, 25, 11)
	LS.AddLabel(1, 1, 2, "Im a label")
	LS.AddLabel(1, 1, 2, "Hi, im another label")
	LS.AddSlider(1, 1, 3, "Fun4", "Fun4 Slider", 5, 25, 11)
	LS.AddCheckbox(1, 1, 3, "Ch2", "Checkbox2", true)
	LS.AddDropdown(1, 1, 3, "SomeDropdown", "DropdownTest", "123", "Option1", "Option2", "123")
	LS.AddCheckbox(1, 1, 3, "Ch3", "Checkbox3", false)
	LS.AddCheckbox(1, 1, 4, "Ch322", "CheckboxHi", false)
	LS.AddDropdown(1, 1, 5, "SomeDropdownHello", "DropdownTest123", "123", "Option1", "Option2", "123")
	LS.AddTextbox(1, 1, 5, "TextVar1", "Testing Textbox", "Hi, im a test")

	LS.AddLabel(2, 1, 0, "This is a test")
	LS.AddLabel(2, 1, 0, "This is another test")
	LS.AddLabel(2, 1, 1, "Another label, line 1")

	LS.InitButtonMain("Main", "xxxxx")

	LS.InitToggle("Cooldowns", "CDs", false, "")

	LS.InitToggle("AOE", "AOE", false, "Test explanation")

	LS.InitToggle("Third Toggle", "T12T", true, "Test")

end

function LS.InitTabs(...)
	local arg = {...}

	--Hardcode second to last tab as Trinkets
	arg[#arg+1] = "Trinkets"

	--Hardcode last tab as Pots
	arg[#arg+1] = "Potions"

	--Set the Tabs' Frame backdrop
	local topWindowBackdrop ={
		bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background-Dark",
 		edgeFile = "Interface\\Addons\\LegendarySettings\\Vectors\\border",
		tile = true,
		tileEdge = true,
		tileSize = 16,
		edgeSize = 16,
		insets = { left = 3, right = 5, top = 3, bottom = 5 },
	}

	local backdropInfo ={
		--bgFile = "Interface\\Tooltips\\UI-Tooltip-Background",
 		edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
 		tile = true,
 		tileEdge = true,
 		tileSize = 8,
 		edgeSize = 8,
 		insets = { left = 1, right = 1, top = 1, bottom = 1 },
	}

	local texture = SettingsFrameIconHeader:CreateTexture()
	texture:SetAllPoints()
	texture:SetPoint("TOPLEFT", SettingsFrameIconHeader ,"TOPLEFT", 125, -0.95)
	texture:SetPoint("BOTTOMRIGHT", SettingsFrameIconHeader ,"BOTTOMRIGHT", -125, 0.95)
	texture:SetTexture("Interface\\Addons\\LegendarySettings\\Vectors\\legendary")
	SettingsFrameIconHeader.texture = texture

	SettingsFrameTabs:SetBackdrop(backdropInfo);
	SettingsFrameIconHeader:SetBackdrop(backdropInfo);

	SettingsFrame:SetBackdrop(topWindowBackdrop);
	--SettingsFrame:SetBackdropBorderColor(0.9, 0.9 ,0.1, 1.0);

	LoadSaveButton:SetSize(LS.TabButtonSizeX, LS.TabButtonSizeY)
	LoadSaveButton:SetPoint("TOPLEFT", SettingsFrameTabs, "BOTTOMLEFT", LS.TabOffsetX, LS.TabOffsetY+LS.TabButtonSizeY)
	LoadSaveButton:SetText("Profiles")
	LoadSaveButton:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
	LoadSaveButton:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	LoadSaveButton:SetNormalFontObject(_G["legendaryFontButtonNormal"])
	LoadSaveButton:SetHighlightFontObject(_G["legendaryFontButtonSelected"])

	CommandsButton:SetSize(LS.TabButtonSizeX, LS.TabButtonSizeY)
	CommandsButton:SetPoint("TOPLEFT", SettingsFrameTabs, "BOTTOMLEFT", LS.TabOffsetX, LS.TabOffsetY+LS.TabButtonSizeY + LS.TabButtonSizeY +LS.TabButtonsSpacingY)
	CommandsButton:SetText("Commands")
	CommandsButton:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
	CommandsButton:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	CommandsButton:SetNormalFontObject(_G["legendaryFontButtonNormal"])
	CommandsButton:SetHighlightFontObject(_G["legendaryFontButtonSelected"])

	for i=1,#arg do
		LS.Tabs[i] = {}
		--LS.Tabs[i].Lines = {}

		LS.Tabs[i].CategoriesBody = CreateFrame("Frame", "SettingsFrameTab"..i, SettingsFrame, "BackdropTemplate")
		LS.Tabs[i].CategoriesBody:SetPoint("TOPRIGHT", SettingsFrame, "TOPRIGHT", -10, -10)
		LS.Tabs[i].CategoriesBody:SetSize(LS.TabBodySizeX, LS.TabBodyCategoriesSizeY)
		LS.Tabs[i].CategoriesBody:Hide();
		LS.Tabs[i].CategoriesBody:SetBackdrop(backdropInfo)
	
		LS.Tabs[i].MiniTabs = {}

		LS.Tabs[i].Button = CreateFrame("Button", nil, SettingsFrameTabs, "UIPanelButtonTemplate")
		LS.Tabs[i].Button:SetPoint("TOPLEFT", SettingsFrameTabs, "TOPLEFT", LS.TabOffsetX, -LS.TabOffsetY + LS.TabNextOffsetY)
		LS.Tabs[i].Button:SetSize(LS.TabButtonSizeX, LS.TabButtonSizeY)
		LS.Tabs[i].Button:SetText(arg[i])
		LS.Tabs[i].Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
		LS.Tabs[i].Button:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		LS.Tabs[i].Button:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		LS.Tabs[i].Button:SetHighlightFontObject(_G["legendaryFontButtonSelected"])

		LS.Tabs[i].Button:SetScript("OnClick", function(self, button, down)
			LS.ToggleTab(i, 1)
		end)
		LS.Tabs[i].Button:RegisterForClicks("AnyDown", "AnyUp")

		LS.TabNextOffsetY = LS.TabNextOffsetY - LS.TabButtonSizeY -LS.TabButtonsSpacingY;
	end
	SettingsFrameTabProfiles:Hide();

	--Hardcode minitabs for trinkets
	LS.InitMiniTabs(#arg-1, "Top", "Bottom")

	--Hardcode trinket settings
	LS.AddDropdown(#arg-1, 1, 0, "TopTrinketCondition", "Top Trinket Usage", "With Hekili", "At HP", "With Hekili", "Don't Use");
	LS.AddDropdown(#arg-1, 1, 0, "TopTrinketTarget", "Top Trinket Target", "Enemy", "Enemy", "Player", "Cursor", "Friendly");
	LS.AddDropdown(#arg-1, 1, 1, "TopTrinketCursor", "Top Trinket Cursor Settings", "Enemy Under Cursor", "Confirmation", "Cursor", "Enemy Under Cursor");
	LS.AddSlider(#arg-1, 1, 1, "TopTrinketHP", "Top Trinket @ HP", 0, 100, 80);

	LS.AddDropdown(#arg-1, 2, 0, "BottomTrinketCondition", "Bottom Trinket Usage", "With Hekili", "At HP", "With Hekili", "Don't Use");
	LS.AddDropdown(#arg-1, 2, 0, "BottomTrinketTarget", "Bottom Trinket Target", "Enemy", "Enemy", "Player", "Cursor", "Friendly");
	LS.AddDropdown(#arg-1, 2, 1, "BottomTrinketCursor", "Bottom Trinket Cursor Settings", "Enemy Under Cursor", "Confirmation", "Cursor", "Enemy Under Cursor");
	LS.AddSlider(#arg-1, 2, 1, "BottomTrinketHP", "Bottom Trinket @ HP", 0, 100, 80);

	--Hardcode minitabs for Pots
	LS.InitMiniTabs(#arg, "DPS Potions")

	--Hardcode pot settings
	LS.AddDropdown(#arg, 1, 0, "DPSPotionUsage", "DPS Potion With", "Bloodlust+Cooldowns", "Cooldowns", "Bloodlust", "Bloodlust+Cooldowns", "On Cooldown", "Don't Use");
	LS.AddDropdown(#arg, 1, 1, "DPSPotionName", "DPS Potion Name", "Ultimate Power", "Fleeting Ultimate Power", "Ultimate Power", "Fleeting Power", "Power", "Shocking Disclosure");
end

function LS.InitMiniTabs(tab, ...)
	local arg = {...}

	local backdropInfo ={
		--bgFile = "Interface\\Tooltips\\UI-Tooltip-Background",
 		edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
 		tile = true,
 		tileEdge = true,
 		tileSize = 8,
 		edgeSize = 8,
 		insets = { left = 1, right = 1, top = 1, bottom = 1 },
	}

	LS.MiniTabNextOffsetX = 0
	
	for i=1,#arg do
		LS.Tabs[tab].MiniTabs[i] = {}
		LS.Tabs[tab].MiniTabs[i].Lines = {}

		LS.Tabs[tab].MiniTabs[i].Body = CreateFrame("Frame", "SettingsFrameTab"..i, SettingsFrame, "BackdropTemplate")
		LS.Tabs[tab].MiniTabs[i].Body:SetPoint("BOTTOMRIGHT", SettingsFrame, "BOTTOMRIGHT", -10, 10)
		LS.Tabs[tab].MiniTabs[i].Body:SetSize(LS.TabBodySizeX, LS.TabBodySizeY)
		LS.Tabs[tab].MiniTabs[i].Body:Hide();
		LS.Tabs[tab].MiniTabs[i].Body:SetBackdrop(backdropInfo)
		LS.Tabs[tab].MiniTabs[i].Body:SetScript("OnMouseDown", function(self, button, down)
			LS.MinimizeDropdowns(nil)
		end)

		LS.Tabs[tab].MiniTabs[i].Button = CreateFrame("Button", nil, LS.Tabs[tab].CategoriesBody, "UIPanelButtonTemplate")
		LS.Tabs[tab].MiniTabs[i].Button:SetPoint("BOTTOMLEFT", LS.Tabs[tab].CategoriesBody, "BOTTOMLEFT", LS.MiniTabOffsetX + LS.MiniTabNextOffsetX, LS.MiniTabOffsetY)
		LS.Tabs[tab].MiniTabs[i].Button:SetSize(LS.MiniTabButtonSizeX, LS.MiniTabButtonSizeY)
		LS.Tabs[tab].MiniTabs[i].Button:SetText(arg[i])
		LS.Tabs[tab].MiniTabs[i].Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
		LS.Tabs[tab].MiniTabs[i].Button:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		LS.Tabs[tab].MiniTabs[i].Button:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
		LS.Tabs[tab].MiniTabs[i].Button:SetHighlightFontObject(_G["legendaryFontButtonSelectedS"])

		LS.Tabs[tab].MiniTabs[i].Button:SetScript("OnClick", function(self, button, down)
			LS.ToggleTab(tab, i)
		end)
		LS.Tabs[tab].MiniTabs[i].Button:RegisterForClicks("AnyDown", "AnyUp")

		LS.MiniTabNextOffsetX = LS.MiniTabNextOffsetX + LS.MiniTabButtonSizeX +LS.MiniTabButtonsSpacingX;
	end

end

function LS.InitMiniButtons()
	SettingsButton:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
	SettingsButton:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	SettingsButton:SetNormalFontObject(_G["legendaryFontButtonNormal"])
	SettingsButton:SetHighlightFontObject(_G["legendaryFontButtonSelected"])

	HideButton:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
	HideButton:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	HideButton:SetNormalFontObject(_G["legendaryFontButtonNormal"])
	HideButton:SetHighlightFontObject(_G["legendaryFontButtonSelected"])
end

function LS.InitProfilesTab()
	local backdropInfo = {
		--bgFile = "Interface\\Tooltips\\UI-Tooltip-Background",
 		edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
 		tile = true,
 		tileEdge = true,
 		tileSize = 8,
 		edgeSize = 8,
 		insets = { left = 1, right = 1, top = 1, bottom = 1 },
	}

	LS.SettingsFrameTabProfiles.CategoriesBody = CreateFrame("Frame", "SettingsFrameTabProfiles", SettingsFrame, "BackdropTemplate")
	LS.SettingsFrameTabProfiles.CategoriesBody:SetPoint("TOPRIGHT", SettingsFrame, "TOPRIGHT", -10, -10)
	LS.SettingsFrameTabProfiles.CategoriesBody:SetSize(LS.TabBodySizeX, LS.TabBodyCategoriesSizeY)
	LS.SettingsFrameTabProfiles.CategoriesBody:Hide();
	LS.SettingsFrameTabProfiles.CategoriesBody:SetBackdrop(backdropInfo)

	LS.SettingsFrameTabProfiles.Body = CreateFrame("Frame", "SettingsFrameTabProfiles", SettingsFrame, "BackdropTemplate")
	LS.SettingsFrameTabProfiles.Body:SetPoint("BOTTOMRIGHT", SettingsFrame, "BOTTOMRIGHT", -10, 10)
	LS.SettingsFrameTabProfiles.Body:SetSize(LS.TabBodySizeX, LS.TabBodySizeY)
	LS.SettingsFrameTabProfiles.Body:Hide();
	LS.SettingsFrameTabProfiles.Body:SetBackdrop(backdropInfo)

	LS.SettingsFrameTabCommands.CategoriesBody = CreateFrame("Frame", "SettingsFrameTabCommandsCategories", SettingsFrame, "BackdropTemplate")
	LS.SettingsFrameTabCommands.CategoriesBody:SetPoint("TOPRIGHT", SettingsFrame, "TOPRIGHT", -10, -10)
	LS.SettingsFrameTabCommands.CategoriesBody:SetSize(LS.TabBodySizeX, LS.TabBodyCategoriesSizeY)
	LS.SettingsFrameTabCommands.CategoriesBody:Hide();
	LS.SettingsFrameTabCommands.CategoriesBody:SetBackdrop(backdropInfo)

	LS.SettingsFrameTabCommands.MiniTabs = {}

	local miniTabNextOffsetXCommands = 0
	local commandTabNames = {"Toggles", "Target", "Player", "Cursor", "Mouseover", "Focus"}

	for i=1,#commandTabNames do
		LS.SettingsFrameTabCommands.MiniTabs[i] = {}
		LS.SettingsFrameTabCommands.MiniTabs[i].Lines = {}
		LS.SettingsFrameTabCommands.MiniTabs[i].NumberOfCommands = 0

		LS.SettingsFrameTabCommands.MiniTabs[i].Body = CreateFrame("Frame", nil, SettingsFrame, "BackdropTemplate")
		LS.SettingsFrameTabCommands.MiniTabs[i].Body:SetPoint("BOTTOMRIGHT", SettingsFrame, "BOTTOMRIGHT", -10, 10)
		LS.SettingsFrameTabCommands.MiniTabs[i].Body:SetSize(LS.TabBodySizeX, LS.TabBodySizeY)
		LS.SettingsFrameTabCommands.MiniTabs[i].Body:Hide();
		LS.SettingsFrameTabCommands.MiniTabs[i].Body:SetBackdrop(backdropInfo)
		LS.SettingsFrameTabCommands.MiniTabs[i].Body:SetScript("OnMouseDown", function(self, button, down)
			LS.MinimizeDropdowns(nil)
		end)

		LS.SettingsFrameTabCommands.MiniTabs[i].Button = CreateFrame("Button", nil, LS.SettingsFrameTabCommands.CategoriesBody, "UIPanelButtonTemplate")
		LS.SettingsFrameTabCommands.MiniTabs[i].Button:SetPoint("BOTTOMLEFT", LS.SettingsFrameTabCommands.CategoriesBody, "BOTTOMLEFT", LS.MiniTabOffsetX + miniTabNextOffsetXCommands, LS.MiniTabOffsetY)
		LS.SettingsFrameTabCommands.MiniTabs[i].Button:SetSize(LS.MiniTabButtonSizeX, LS.MiniTabButtonSizeY)
		LS.SettingsFrameTabCommands.MiniTabs[i].Button:SetText(commandTabNames[i])
		LS.SettingsFrameTabCommands.MiniTabs[i].Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
		LS.SettingsFrameTabCommands.MiniTabs[i].Button:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		LS.SettingsFrameTabCommands.MiniTabs[i].Button:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
		LS.SettingsFrameTabCommands.MiniTabs[i].Button:SetHighlightFontObject(_G["legendaryFontButtonSelectedS"])

		LS.SettingsFrameTabCommands.MiniTabs[i].Button:SetScript("OnClick", function(self, button, down)
			LS.ToggleTab(99, i)
		end)
		LS.SettingsFrameTabCommands.MiniTabs[i].Button:RegisterForClicks("AnyDown", "AnyUp")

		miniTabNextOffsetXCommands = miniTabNextOffsetXCommands + LS.MiniTabButtonSizeX +LS.MiniTabButtonsSpacingX;
	end

	local i = 1
	for _,k in pairs(LS.GetProfileKeysInOrder()) do
		LS.ProfileButtons[k] = CreateFrame("Frame", nil, LS.SettingsFrameTabProfiles.Body, "BackdropTemplate")
		LS.ProfileButtons[k]:SetBackdrop({
			bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
			edgeFile = "Interface\\Addons\\LegendarySettings\\Vectors\\borderActive",
			edgeSize = 16,
			insets = { left = 4, right = 4, top = 4, bottom = 4 },
		})
		if LegendarySettingsDB[LS.SpecID].SelectedProfile == k then
			LS.ProfileButtons[k]:SetBackdropBorderColor(1, 0.9, 0.9, 1)
		else
			LS.ProfileButtons[k]:SetBackdropBorderColor(0.2, 0, 0, 1)
		end
		LS.ProfileButtons[k]:SetPoint("TOPLEFT", LS.SettingsFrameTabProfiles.Body, "TOPLEFT", 10, -8 - 70*(i-1))
		LS.ProfileButtons[k]:SetSize(400,70);

		local Button = CreateFrame("Button", nil, LS.ProfileButtons[k], "UIPanelButtonTemplate")
		Button:SetPoint("TOPLEFT", LS.ProfileButtons[k], "TOPLEFT", 10, -10)
		Button:SetPoint("BOTTOMRIGHT", LS.ProfileButtons[k], "BOTTOMLEFT", 130, 14)
		--Button:SetSize(100, 50)
		Button:SetText(k)
		Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
		Button:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		Button:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		Button:SetHighlightFontObject(_G["legendaryFontButtonSelected"])
		Button:SetScript("OnClick", function(self, button, down)
			LS.ChangeProfile(k)
		end)

		local ButtonDelete = CreateFrame("Button", nil, LS.ProfileButtons[k], "UIPanelButtonTemplate")
		--ButtonDelete:SetPoint("CENTER", LS.ProfileButtons[k], "TOPRIGHT", -50, -35)
		--ButtonDelete:SetSize(80, 50)
		ButtonDelete:SetPoint("TOPLEFT", LS.ProfileButtons[k], "TOPRIGHT", -130, -10)
		ButtonDelete:SetPoint("BOTTOMRIGHT", LS.ProfileButtons[k], "BOTTOMRIGHT", -10, 14)
		ButtonDelete:SetText("Delete Profile")
		ButtonDelete:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
		ButtonDelete:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		ButtonDelete:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		ButtonDelete:SetHighlightFontObject(_G["legendaryFontButtonSelected"])
		ButtonDelete:SetScript("OnClick", function(self, button, down)
			LS.DeleteProfile(k)
		end)

		i = i + 1
	end

	local EditBox = CreateFrame("EditBox", nil, LS.SettingsFrameTabProfiles.Body, "InputBoxTemplate")
	EditBox:SetPoint("TOPRIGHT", LS.SettingsFrameTabProfiles.Body, "TOPRIGHT", -LS.MiniTabOffsetX, -LS.MiniTabOffsetY)
	EditBox:SetSize(LS.MiniTabButtonSizeX-4, LS.MiniTabButtonSizeY)
	EditBox:SetAutoFocus(false)
	EditBox:SetText("Profile Name")
	EditBox:SetFontObject(_G["legendaryFontNormalAccentAlt"])

	local texture = EditBox:CreateTexture()
	texture:SetAllPoints()
	texture:SetPoint("TOPLEFT", EditBox ,"TOPLEFT", -4, 0)
	texture:SetPoint("BOTTOMRIGHT", EditBox ,"BOTTOMRIGHT", 0, 0)
	texture:SetTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Editbox")
	EditBox.texture = texture

	local ButtonCreate = CreateFrame("Button", nil, LS.SettingsFrameTabProfiles.CategoriesBody, "UIPanelButtonTemplate")
	ButtonCreate:SetPoint("BOTTOMRIGHT", LS.SettingsFrameTabProfiles.CategoriesBody, "BOTTOMRIGHT", -LS.MiniTabOffsetX, LS.MiniTabOffsetY)
	ButtonCreate:SetSize(LS.MiniTabButtonSizeX, LS.MiniTabButtonSizeY)
	ButtonCreate:SetText("Create Profile")
	ButtonCreate:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
	ButtonCreate:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	ButtonCreate:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
	ButtonCreate:SetHighlightFontObject(_G["legendaryFontButtonSelectedS"])
	ButtonCreate:SetScript("OnClick", function(self, button, down)
		LS.CreateProfile(EditBox:GetText())
	end)
	
	local ButtonResetToDefault = CreateFrame("Button", nil, LS.SettingsFrameTabProfiles.CategoriesBody, "UIPanelButtonTemplate")
	ButtonResetToDefault:SetPoint("BOTTOMLEFT", LS.SettingsFrameTabProfiles.CategoriesBody, "BOTTOMLEFT", LS.MiniTabOffsetX, LS.MiniTabOffsetY)
	ButtonResetToDefault:SetSize(LS.MiniTabButtonSizeX*2+10, LS.MiniTabButtonSizeY)
	ButtonResetToDefault:SetText("Reset Selected Profile to Default")
	ButtonResetToDefault:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")--1Button BigButtonNotHighlighted
	ButtonResetToDefault:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	ButtonResetToDefault:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
	ButtonResetToDefault:SetHighlightFontObject(_G["legendaryFontButtonSelectedS"])
	ButtonResetToDefault:SetScript("OnClick", function(self, button, down)
		for i, v in pairs(LS.DefaultSettings) do
			LS.Settings[i] = v
		end
		LS.UpdateExistingControls();
	end)

	local ButtonLockETESPos = CreateFrame("Button", nil, LS.SettingsFrameTabProfiles.CategoriesBody, "UIPanelButtonTemplate")
	ButtonLockETESPos:SetPoint("BOTTOMLEFT", LS.SettingsFrameTabProfiles.CategoriesBody, "BOTTOMLEFT", LS.MiniTabOffsetX + LS.MiniTabButtonSizeX*2+10 + LS.MiniTabOffsetX, LS.MiniTabOffsetY)
	ButtonLockETESPos:SetSize(LS.MiniTabButtonSizeX, LS.MiniTabButtonSizeY)
	ButtonLockETESPos:SetText("Lock LS/LT")
	ButtonLockETESPos:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
	ButtonLockETESPos:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	ButtonLockETESPos:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
	ButtonLockETESPos:SetHighlightFontObject(_G["legendaryFontButtonSelectedS"])
	ButtonLockETESPos:SetScript("OnClick", function(self, button, down)
		if SettingsButton:IsMovable() then
			self:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")
			self:SetNormalFontObject(_G["legendaryFontButtonSelectedS"])
			SettingsButton:SetMovable(false);
		else
			ButtonLockETESPos:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
			self:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
			SettingsButton:SetMovable(true);
		end
		if HideButton:IsMovable() then
			HideButton:SetMovable(false);
		else
			HideButton:SetMovable(true);
		end
	end)
	
	--Version label
	LS.SettingsFrameTabProfiles.VersionLabel = CreateFrame("Frame", nil, LS.SettingsFrameTabProfiles.CategoriesBody)
	LS.SettingsFrameTabProfiles.VersionLabel:SetPoint("BOTTOMLEFT", LS.SettingsFrameTabProfiles.CategoriesBody, "BOTTOMLEFT", LS.MiniTabOffsetX + LS.MiniTabButtonSizeX*5+10 + LS.MiniTabOffsetX, LS.MiniTabOffsetY)
	LS.SettingsFrameTabProfiles.VersionLabel:SetSize(LS.MiniTabButtonSizeX*2+10, LS.MiniTabButtonSizeY)
	LS.SettingsFrameTabProfiles.VersionText = LS.SettingsFrameTabProfiles.VersionLabel:CreateFontString(nil,"OVERLAY","GameFontNormal");
	LS.SettingsFrameTabProfiles.VersionText:SetPoint("CENTER");
	LS.SettingsFrameTabProfiles.VersionText:SetText("");
	LS.SettingsFrameTabProfiles.VersionText:SetFontObject(_G["legendaryFontNormal"])

	LS.AddLabelForCommands(1, 0, "These are the Commands to manually control the toggles")
	LS.AddLabelForCommands(2, 0, "These spells can be queued to cast on player")
	LS.AddLabelForCommands(2, 1, "If you want to queue other spells, ask the responsible Dev")
	LS.AddLabelForCommands(3, 0, "These spells can be queued to cast on target")
	LS.AddLabelForCommands(4, 0, "These spells can be queued to cast on cursor")
	LS.AddLabelForCommands(4, 1, "If you want to queue other spells, ask the responsible Dev")
	LS.AddLabelForCommands(5, 0, "These spells can be queued to cast on mouseover")
	LS.AddLabelForCommands(5, 1, "If you want to queue other spells, ask the responsible Dev")
	LS.AddLabelForCommands(6, 0, "These spells can be queued to cast on focus")
	LS.AddLabelForCommands(6, 1, "If you want to queue other spells, ask the responsible Dev")
	

	--[[
	local ButtonLockUnlockToggles = CreateFrame("Button", nil, SettingsFrameTabProfiles, "UIPanelButtonTemplate")
	ButtonResetToDefault:SetPoint("TOPRIGHT", SettingsFrameTabProfiles, "BOTTOMRIGHT", -10, 60)
	ButtonResetToDefault:SetSize(100, 50)
	ButtonResetToDefault:SetText("Lock Toggles' Position")
	ButtonResetToDefault:SetScript("OnClick", function(self, button, down)
		if FrameToggles:IsMoveable() then
			FrameToggles.SetMoveable(false);
			self:SetText("Unlock Toggles' Position")
		else
			FrameToggles.SetMoveable(true);
			self:SetText("Lock Toggles' Position")
		end
	end)
	--]]

end

function LS.ChangeProfile(profile)
	for k,v in pairs(LS.ProfileButtons) do
		if k == profile then
			v:SetBackdropBorderColor(1, 0.9, 0.9, 1)
		else
			v:SetBackdropBorderColor(0.2, 0, 0, 1)
		end
	end

	if LegendarySettingsDB[LS.SpecID].SelectedProfile then
		for i, v in pairs(LS.Settings) do
			LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile][i] = v
		end
	end

	LegendarySettingsDB[LS.SpecID].SelectedProfile = profile

	-- Update Settings to the loaded profile's ones
	for i, v in pairs(LegendarySettingsDB[LS.SpecID].Profiles[profile]) do
		LS.Settings[i] = v
	end

	LS.UpdateExistingControls();
end


-- /run print(LegendarySettings.GetProfileKeysInOrder()[1])
function LS.GetProfileKeysInOrder()
	local keysInAscendingOrder = {}
	local ids = {}
	local i = 1

	for k,v in pairs(LegendarySettingsDB[LS.SpecID].Profiles) do
		keysInAscendingOrder[i] = k;
		i = i+1
	end

	return keysInAscendingOrder
end

function LS.CreateProfile(profile)
	local currentProfileCount = 0
	for k, v in pairs(LegendarySettingsDB[LS.SpecID].Profiles) do
		if v then
			currentProfileCount = currentProfileCount + 1
		end
	end

	if LegendarySettingsDB[LS.SpecID].Profiles[profile] then
		LS.CreateProfile(profile.."_")
		return
	end

	if currentProfileCount >= LS.MaxProfiles then
		return
	end
	
	local profileID = 0
	
	if currentProfileCount > 0 then
		profileID = LegendarySettingsDB[LS.SpecID].Profiles[LS.GetProfileKeysInOrder()[1]].ID + 1
	end

	LegendarySettingsDB[LS.SpecID].Profiles[profile] = {}

	for i, v in pairs(LS.Settings) do
		LegendarySettingsDB[LS.SpecID].Profiles[profile][i] = v
	end

	LegendarySettingsDB[LS.SpecID].Profiles[profile].ID = profileID
	
	--Add a new Profile Button
	
	LS.ProfileButtons[profile] = CreateFrame("Frame", nil, LS.SettingsFrameTabProfiles.Body, "BackdropTemplate")
	LS.ProfileButtons[profile]:SetBackdrop({
		bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
		edgeFile = "Interface\\Addons\\LegendarySettings\\Vectors\\borderActive",
		edgeSize = 16,
		insets = { left = 4, right = 4, top = 4, bottom = 4 },
	})
	LS.ProfileButtons[profile]:SetBackdropBorderColor(1, 0.9, 0.9, 1)
	LS.ProfileButtons[profile]:SetPoint("TOPLEFT", LS.SettingsFrameTabProfiles.Body, "TOPLEFT", 10, -8 - 70*(currentProfileCount))
	LS.ProfileButtons[profile]:SetSize(400,70);

	local ButtonDelete = CreateFrame("Button", nil, LS.ProfileButtons[profile], "UIPanelButtonTemplate")
	ButtonDelete:SetPoint("TOPLEFT", LS.ProfileButtons[profile], "TOPRIGHT", -130, -10)
	ButtonDelete:SetPoint("BOTTOMRIGHT", LS.ProfileButtons[profile], "BOTTOMRIGHT", -10, 14)
	ButtonDelete:SetText("Delete Profile")
	ButtonDelete:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
	ButtonDelete:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	ButtonDelete:SetNormalFontObject(_G["legendaryFontButtonNormal"])
	ButtonDelete:SetHighlightFontObject(_G["legendaryFontButtonSelected"])
	ButtonDelete:SetScript("OnClick", function(self, button, down)
		LS.DeleteProfile(profile)
	end)

	local Button = CreateFrame("Button", nil, LS.ProfileButtons[profile], "UIPanelButtonTemplate")
	Button:SetPoint("TOPLEFT", LS.ProfileButtons[profile], "TOPLEFT", 10, -10)
	Button:SetPoint("BOTTOMRIGHT", LS.ProfileButtons[profile], "BOTTOMLEFT", 130, 14)
	Button:SetText(profile)
	Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
	Button:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	Button:SetNormalFontObject(_G["legendaryFontButtonNormal"])
	Button:SetHighlightFontObject(_G["legendaryFontButtonSelected"])
	Button:SetScript("OnClick", function(self, button, down)
		LS.ChangeProfile(profile)
	end)

	--Change the current Profile
	LS.ChangeProfile(profile)
end

function LS.DeleteProfile(profile)
	LegendarySettingsDB[LS.SpecID].Profiles[profile] = nil

	LS.ProfileButtons[profile]:Hide()

	if LegendarySettingsDB[LS.SpecID].SelectedProfile == profile then
		if LS.GetProfileKeysInOrder()[1] then
			LegendarySettingsDB[LS.SpecID].SelectedProfile = LS.GetProfileKeysInOrder()[1]
			LS.ChangeProfile(LS.GetProfileKeysInOrder()[1])
		else
			LegendarySettingsDB[LS.SpecID].SelectedProfile = nil
		end
	end

	LS.ReorderProfileFrame()
end

function LS.ReorderProfileFrame()
	local i = 1
	for _,k in pairs(LS.GetProfileKeysInOrder()) do
		LS.ProfileButtons[k]:SetPoint("TOPLEFT", LS.SettingsFrameTabProfiles.Body, "TOPLEFT", 10, -8 - 80*(i-1))
		i = i + 1
	end

end

function LS.ToggleTab(tab, minitab)
	for i,v in ipairs(LS.Tabs) do 
		if i == tab then
			for j,u in ipairs(LS.Tabs[i].MiniTabs) do 
				if j == minitab then
					u.Body:Show();
					u.Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")--2ndtry 
					u.Button:SetNormalFontObject(_G["legendaryFontButtonSelectedS"])
				else
					u.Body:Hide();
					u.Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
					u.Button:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
				end
			end
			v.CategoriesBody:Show();
			v.Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")--2ndtry
			v.Button:SetNormalFontObject(_G["legendaryFontButtonSelected"])
		else
			for j,u in ipairs(LS.Tabs[i].MiniTabs) do 
				u.Body:Hide();
				u.Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
				u.Button:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
			end
			v.CategoriesBody:Hide();
			v.Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") --BigButtonS
			v.Button:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		end
	end
	if tab == 0 then
		LS.SettingsFrameTabProfiles.Body:Show();
		LS.SettingsFrameTabProfiles.CategoriesBody:Show();
		LoadSaveButton:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")--2ndtry
		LoadSaveButton:SetNormalFontObject(_G["legendaryFontButtonSelected"])
	else
		LS.SettingsFrameTabProfiles.Body:Hide();
		LS.SettingsFrameTabProfiles.CategoriesBody:Hide();
		LoadSaveButton:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
		LoadSaveButton:SetNormalFontObject(_G["legendaryFontButtonNormal"])
	end
	if tab == 99 then
		for j,u in ipairs(LS.SettingsFrameTabCommands.MiniTabs) do 
			if j == minitab then
				u.Body:Show();
				u.Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")--2ndtry 
				u.Button:SetNormalFontObject(_G["legendaryFontButtonSelectedS"])
			else
				u.Body:Hide();
				u.Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
				u.Button:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
			end
		end
		LS.SettingsFrameTabCommands.CategoriesBody:Show();
		CommandsButton:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")--2ndtry
		CommandsButton:SetNormalFontObject(_G["legendaryFontButtonSelected"])
	else
		for j,u in ipairs(LS.SettingsFrameTabCommands.MiniTabs) do 
			u.Body:Hide();
			u.Button:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
			u.Button:SetNormalFontObject(_G["legendaryFontButtonNormalS"])
		end
		LS.SettingsFrameTabCommands.CategoriesBody:Hide();
		CommandsButton:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") --BigButtonS
		CommandsButton:SetNormalFontObject(_G["legendaryFontButtonNormal"])
	end
	LS.MinimizeDropdowns(nil)
	--LS.SettingsFrameTabProfiles.Body:Hide();
end

function LS.MinimizeDropdowns(dropdownName)
	--Close Dropdowns
	for i,v in pairs(LS.Tabs) do 
		for _,m in pairs(v.MiniTabs) do 
			for _,l in pairs(m.Lines) do 
				for k,u in pairs(l.Controls) do
					local controlName = u:GetName()
					if controlName ~= dropdownName then
						if string.find(controlName, "DROPDOWN") then
							for _,t in pairs(u.optionControls) do
								t:Hide()
							end
						end
					end
				end
			end
		end
	end
end

function LS.UpdateExistingControls()
	for i=1,#LS.Tabs do
		for k=1,#LS.Tabs[i].MiniTabs do
			--for j=0,#LS.Tabs[i].MiniTabs[k].Lines-1 do
			for _,u in pairs(LS.Tabs[i].MiniTabs[k].Lines) do
				for k,v in pairs(u.Controls) do
					local controlName = v:GetName()
					--Dropdowns
					if string.find(controlName, "DROPDOWN") then
						local variableName = string.sub(controlName, 9, #controlName)
						--UIDropDownMenu_SetText(v, LS.Settings[variableName])
						v:SetText(LS.Settings[variableName])
					end
					--Sliders
					if string.find(controlName, "SLIDER") then
						local variableName = string.sub(controlName, 7, #controlName)
						v:SetValue(LS.Settings[variableName])
					end
					--Checkboxes
					if string.find(controlName, "CHECKBOX") then
						local variableName = string.sub(controlName, 9, #controlName)
						v:SetChecked(LS.Settings[variableName])
					end
					--Textboxes
					if string.find(controlName, "TEXTBOX") then
						local variableName = string.sub(controlName, 8, #controlName)
						v:SetText(LS.Settings[variableName])
					end
				end
			end
		end
	end
end

function LS.CreateDropdownControl(name, parent, positionX, positionY, width, height, default, optionsTable)
	local optionHeight = 15;
	
	local f = CreateFrame("Button", "DROPDOWN"..name, parent, "UIPanelButtonTemplate")
	f:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\dropdown")
	f:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
	f:SetNormalFontObject(_G["legendaryFontNormal"])
	f:SetHighlightFontObject(_G["legendaryFontNormalAccent"])
	f:SetSize(width, height)
	f:SetPoint("CENTER", parent, "TOPLEFT", positionX, positionY)
	f:SetText(default)

	f.options = optionsTable
	f.optionControls = {}
	
	--Create Buttons For Options
	for i=1,#f.options do
		f.optionControls[i] = CreateFrame("Button", nil, f, "UIPanelButtonTemplate")
		f.optionControls[i]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Editbox")
		f.optionControls[i]:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		f.optionControls[i]:SetNormalFontObject(_G["legendaryFontNormal"])
		f.optionControls[i]:SetHighlightFontObject(_G["legendaryFontNormalAccent"])
		f.optionControls[i]:SetText(f.options[i])
		f.optionControls[i]:SetSize(width, optionHeight)
		f.optionControls[i]:SetPoint("TOPLEFT", f, "BOTTOMLEFT", 0, -optionHeight*(i-1))
		
		f.optionControls[i]:SetScript("OnClick", function(self, button, down)
			f:SetText(f.options[i])
			LS.Settings[name] = f.options[i]
			for k, v in pairs(f.optionControls) do
				v:Hide()
			end
		end)

		f.optionControls[i]:Hide()
	end
	
	f:SetScript("OnClick", function(self, button, down)
		for k, v in pairs(f.optionControls) do
			if v:IsVisible() then
				v:Hide()
			else
				v:Show()
			end
		end
		LS.MinimizeDropdowns(f:GetName())
	end)
	
	return f;
end

-- Dropdown
function LS.AddDropdown(tab, minitab, line, variable, label, default, ...)
	local arg = {...}

	LS.DefaultSettings[variable] = default

	local currentValue = LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile][variable] or default

	if not LS.Tabs[tab].MiniTabs[minitab].Lines[line] then
		LS.Tabs[tab].MiniTabs[minitab].Lines[line] = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = 0
	end

	local frame=CreateFrame("Frame","DropdownLabel"..variable,LS.Tabs[tab].MiniTabs[minitab].Body);
	frame:SetPoint("BOTTOM", LS.Tabs[tab].MiniTabs[minitab].Body, "TOPLEFT", 80 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset, -LS.SettingControlHeight - LS.SpacingBetweenLines*line)
	frame:SetSize(100,LS.SettingControlHeight);
 
	local text=frame:CreateFontString(nil,"OVERLAY","GameFontNormal");
	text:SetPoint("CENTER");
	text:SetText(label);
	text:SetFontObject(_G["legendaryFontNormal"])

	--local dropDown = CreateFrame("Frame", "DROPDOWN"..variable, LS.Tabs[tab].Body, "UIDropDownMenuTemplate")

	local dropDown = LS.CreateDropdownControl(variable, LS.Tabs[tab].MiniTabs[minitab].Body, 80 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset, -LS.SettingControlHeight - LS.SpacingBetweenLines*line, 130, 20, currentValue, arg)

	--local texture = dropDown:CreateTexture()
	--texture:SetAllPoints()
	--texture:SetPoint("TOPLEFT", dropDown ,"TOPLEFT", 14, -3)
	--texture:SetPoint("BOTTOMRIGHT", dropDown ,"BOTTOMRIGHT", -14, 7)
	--texture:SetTexture("Interface\\Addons\\LegendarySettings\\Vectors\\dropdown2")
	--dropDown.texture = texture

	--dropDown:SetBackdrop({
	--	bgFile = "Interface\\Addons\\LegendarySettings\\Vectors\\dropdown",
	--	edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Gold-Border",
	--	edgeSize = 16,
	--	insets = { left = 4, right = 4, top = 4, bottom = 4 },
	--})
	--/run print(_G[_G["DROPDOWNSomeDropdown"]:GetChildren():GetName()]:GetNumRegions()) 4
	--/run print(select(2, _G["DROPDOWNSomeDropdown"]:GetRegions()):GetFrameType()) 5

	--/run print(_G["DROPDOWNSomeDropdownBackdrop"]) 5

	--/run print(select(1, _G[_G["DROPDOWNSomeDropdown"]:GetChildren():GetName()]:GetRegions()):GetName()) 4

	--_G[dropDown:GetName() .. 'Button']:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\dropdownbutton")
	--for i,v in ipairs(_G[dropDown:GetName()]) do 
	--	print(i)
	--end

	--dropDown:SetPoint("LEFT", LS.Tabs[tab].Body, "TOPLEFT", -10 + LS.Tabs[tab].Lines[line].NextOffset, -LS.SettingControlHeight -2 - LS.SpacingBetweenLines*line)
	--dropDown:SetNormalFontObject(_G["legendaryFontNormal"])
	--_G[dropDown:GetName() .. 'Text']:SetFontObject(_G["legendaryFontNormalAccent"])
	--UIDropDownMenu_SetWidth(dropDown, 130)
	--UIDropDownMenu_SetButtonWidth(dropDown, 130)
	--UIDropDownMenu_SetAnchor(dropDown, 25, 20, "TOPLEFT", dropDown, "BOTTOMLEFT")
	--UIDropDownMenu_Initialize(dropDown, function(self, level, menuList)
	--local info = UIDropDownMenu_CreateInfo()
	--info.fontObject = _G["legendaryFontNormalAccent"]
	--for i=1,#arg do
	--	info.text, info.arg1 = arg[i], i

		--local f = CreateFrame("Frame", nil, LS.Tabs[tab].Body, "UIDropDownCustomMenuEntryTemplate")
		--f:SetWidth(130)
		--f:SetHeight(20)

	--	info.customFrame = f;
	--	info.func = function(self, arg1, arg2, checked)
	--		UIDropDownMenu_SetText(dropDown, arg[i])
	--		LS.Settings[variable] = arg[i]
	--		CloseDropDownMenus()
	--	end
	--	UIDropDownMenu_AddButton(info)
	--	end
	--end)
	--UIDropDownMenu_SetText(dropDown, currentValue)

	--Init value
	LS.Settings[variable] = currentValue

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls[#LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls + 1] = dropDown

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset + LS.ControlsSpacingX--7*#label + 125

	return dropDown;
end

-- Group Dropdown
function LS.AddGroupDropdown(tab, minitab, line, variable, label, includeHealers, includeDamagers, includeTanks, includePlayer)
	local dropdown = LS.AddDropdown(tab, minitab, line, variable, label, "party1", "party1", "party2", "party3", "party4")

	do
		--Get Current party
		local PartyUnits = {}
		if includePlayer then
			table.insert(PartyUnits, "player");
		end
		for i = 1, 4 do
			local PartyUnitKey = string.format("party%d", i);
			if UnitExists(PartyUnitKey) then
				if (UnitGroupRolesAssigned(PartyUnitKey) == "HEALER" and includeHealers) or (UnitGroupRolesAssigned(PartyUnitKey) == "DAMAGER" and includeDamagers) or (UnitGroupRolesAssigned(PartyUnitKey) == "TANK" and includeTanks) then
					table.insert(PartyUnits, PartyUnitKey);
				end
			end
		end

		for i = 1, 40 do
			local RaidUnitKey = string.format("raid%d", i);
			if UnitExists(RaidUnitKey) then
				if (UnitGroupRolesAssigned(RaidUnitKey) == "HEALER" and includeHealers) or (UnitGroupRolesAssigned(RaidUnitKey) == "DAMAGER" and includeDamagers) or (UnitGroupRolesAssigned(RaidUnitKey) == "TANK" and includeTanks) then
					table.insert(PartyUnits, RaidUnitKey);
				end
			end
		end

		--Delete old Option buttons
		for i=1,#dropdown.optionControls do
			dropdown.optionControls[i] = nil
			table.remove(dropdown.optionControls, i)
			dropdown.options[i] = nil
			table.remove(dropdown.options, i)
		end

		--Create a Default "None" button
		dropdown.optionControls[1] = CreateFrame("Button", nil, dropdown, "UIPanelButtonTemplate")
		dropdown.optionControls[1]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Editbox")
		dropdown.optionControls[1]:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		dropdown.optionControls[1]:SetNormalFontObject(_G["legendaryFontNormal"])
		dropdown.optionControls[1]:SetHighlightFontObject(_G["legendaryFontNormalAccent"])
		dropdown.optionControls[1]:SetText("None")
		dropdown.optionControls[1]:SetSize(130, 15)
		dropdown.optionControls[1]:SetPoint("TOPLEFT", dropdown, "BOTTOMLEFT", 0, 0)

		dropdown.optionControls[1]:SetScript("OnClick", function(self, button, down)
			dropdown:SetText("None")
			LS.Settings[variable] = "None"
			for k, v in pairs(dropdown.optionControls) do
				v:Hide()
			end
		end)

		dropdown.optionControls[1]:Hide()

		--Create new Option buttons
		for i=2,(#PartyUnits+1) do
			dropdown.optionControls[i] = CreateFrame("Button", nil, dropdown, "UIPanelButtonTemplate")
			dropdown.optionControls[i]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Editbox")
			dropdown.optionControls[i]:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
			if (GetLocale() == "koKR") then
				dropdown.optionControls[i]:SetNormalFontObject(_G["legendaryFontKorNormal"])
				dropdown.optionControls[i]:SetHighlightFontObject(_G["legendaryFontKorNormalAccent"])
			else
				dropdown.optionControls[i]:SetNormalFontObject(_G["legendaryFontNormal"])
				dropdown.optionControls[i]:SetHighlightFontObject(_G["legendaryFontNormalAccent"])
			end
			dropdown.optionControls[i]:SetText(UnitName(PartyUnits[i-1]))
			dropdown.optionControls[i]:SetSize(130, 15)
			dropdown.optionControls[i]:SetPoint("TOPLEFT", dropdown, "BOTTOMLEFT", 0, -15*(i-1))

			dropdown.optionControls[i]:SetScript("OnClick", function(self, button, down)
				dropdown:SetText(UnitName(PartyUnits[i-1]))
				LS.Settings[variable] = UnitName(PartyUnits[i-1])
				for k, v in pairs(dropdown.optionControls) do
					v:Hide()
				end
			end)

			dropdown.optionControls[i]:Hide()
		end
	end

	dropdown:RegisterEvent("GROUP_ROSTER_UPDATE");
	local function eventHandler(self, event, ...)
		if event == "GROUP_ROSTER_UPDATE" then
			local selectedUnitStillExits = false
			--Get Current party
			local PartyUnits = {}
			if includePlayer then
				if LS.Settings[variable] == UnitName("player") then
					selectedUnitStillExits = true
				end
				table.insert(PartyUnits, "player");
			end
			for i = 1, 4 do
				local PartyUnitKey = string.format("party%d", i);
				if UnitExists(PartyUnitKey) then
					if (UnitGroupRolesAssigned(PartyUnitKey) == "HEALER" and includeHealers) or (UnitGroupRolesAssigned(PartyUnitKey) == "DAMAGER" and includeDamagers) or (UnitGroupRolesAssigned(PartyUnitKey) == "TANK" and includeTanks) then
						if LS.Settings[variable] == UnitName(PartyUnitKey) then
							selectedUnitStillExits = true
						end
						table.insert(PartyUnits, PartyUnitKey);
					end
				end
			end

			for i = 1, 40 do
				local RaidUnitKey = string.format("raid%d", i);
				if UnitExists(RaidUnitKey) then
					if (UnitGroupRolesAssigned(RaidUnitKey) == "HEALER" and includeHealers) or (UnitGroupRolesAssigned(RaidUnitKey) == "DAMAGER" and includeDamagers) or (UnitGroupRolesAssigned(RaidUnitKey) == "TANK" and includeTanks) then
						if LS.Settings[variable] == UnitName(RaidUnitKey) then
							selectedUnitStillExits = true
						end
						table.insert(PartyUnits, RaidUnitKey);
					end
				end
			end

			--Delete old Option buttons
			for i=1,#dropdown.optionControls do
				dropdown.optionControls[i] = nil
				table.remove(dropdown.optionControls, i)
				dropdown.options[i] = nil
				table.remove(dropdown.options, i)
			end

			--Create a Default "None" button
			dropdown.optionControls[1] = CreateFrame("Button", nil, dropdown, "UIPanelButtonTemplate")
			dropdown.optionControls[1]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Editbox")
			dropdown.optionControls[1]:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
			dropdown.optionControls[1]:SetNormalFontObject(_G["legendaryFontNormal"])
			dropdown.optionControls[1]:SetHighlightFontObject(_G["legendaryFontNormalAccent"])
			dropdown.optionControls[1]:SetText("None")
			dropdown.optionControls[1]:SetSize(130, 15)
			dropdown.optionControls[1]:SetPoint("TOPLEFT", dropdown, "BOTTOMLEFT", 0, 0)
			
			dropdown.optionControls[1]:SetScript("OnClick", function(self, button, down)
				dropdown:SetText("None")
				LS.Settings[variable] = "None"
				for k, v in pairs(dropdown.optionControls) do
					v:Hide()
				end
			end)

			dropdown.optionControls[1]:Hide()

			--Create new Option buttons
			for i=2,#PartyUnits+1 do
				dropdown.optionControls[i] = CreateFrame("Button", nil, dropdown, "UIPanelButtonTemplate")
				dropdown.optionControls[i]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Editbox")
				dropdown.optionControls[i]:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
				if (GetLocale() == "koKR") then
					dropdown.optionControls[i]:SetNormalFontObject(_G["legendaryFontKorNormal"])
					dropdown.optionControls[i]:SetHighlightFontObject(_G["legendaryFontKorNormalAccent"])
				else
					dropdown.optionControls[i]:SetNormalFontObject(_G["legendaryFontNormal"])
					dropdown.optionControls[i]:SetHighlightFontObject(_G["legendaryFontNormalAccent"])
				end
				dropdown.optionControls[i]:SetText(UnitName(PartyUnits[i-1]))
				dropdown.optionControls[i]:SetSize(130, 15)
				dropdown.optionControls[i]:SetPoint("TOPLEFT", dropdown, "BOTTOMLEFT", 0, -15*(i-1))
				
				dropdown.optionControls[i]:SetScript("OnClick", function(self, button, down)
					dropdown:SetText(UnitName(PartyUnits[i-1]))
					LS.Settings[variable] = UnitName(PartyUnits[i-1])
					for k, v in pairs(dropdown.optionControls) do
						v:Hide()
					end
				end)

				dropdown.optionControls[i]:Hide()
			end
			
			--Set selected option to None if the unit left the party
			if not selectedUnitStillExits then
				dropdown:SetText("None")
			end
		end
	end
	dropdown:SetScript("OnEvent", eventHandler);

end

-- Label
function LS.AddLabel(tab, minitab, line, label)
	if not LS.Tabs[tab].MiniTabs[minitab].Lines[line] then
		LS.Tabs[tab].MiniTabs[minitab].Lines[line] = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = 0
	end

	local frame=CreateFrame("Frame","TextboxLabel"..label,LS.Tabs[tab].MiniTabs[minitab].Body);
	frame:SetPoint("LEFT", LS.Tabs[tab].MiniTabs[minitab].Body, "TOPLEFT", 10 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset,  -30 - LS.SpacingBetweenLines*line)
	frame:SetSize(7*#label,LS.SettingControlHeight);

	local text=frame:CreateFontString(nil,"OVERLAY","GameFontNormal");
	text:SetPoint("LEFT");
	text:SetText(label);
	text:SetFontObject(_G["legendaryFontButtonNormal"])

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls[#LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls + 1] = frame

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset + LS.ControlsSpacingX--7*#label +64

	--EditBox:HookScript("OnClick", function(self, button, down)
	--	LS.MinimizeDropdowns(nil)
	--end)
end

-- Textbox
function LS.AddTextbox(tab, minitab, line, variable, label, default)

	LS.DefaultSettings[variable] = default

	local currentValue = LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile][variable] or default

	if not LS.Tabs[tab].MiniTabs[minitab].Lines[line] then
		LS.Tabs[tab].MiniTabs[minitab].Lines[line] = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = 0
	end

	local frame=CreateFrame("Frame","TextboxLabel"..variable,LS.Tabs[tab].MiniTabs[minitab].Body);
	frame:SetPoint("BOTTOM", LS.Tabs[tab].MiniTabs[minitab].Body, "TOPLEFT", LS.TextboxSizeX/2 +15 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset,  -LS.TextboxSizeY -10 - LS.SpacingBetweenLines*line)
	frame:SetSize(7*#label,LS.SettingControlHeight);

	local text=frame:CreateFontString(nil,"OVERLAY","GameFontNormal");
	text:SetPoint("LEFT");
	text:SetText(label);
	text:SetFontObject(_G["legendaryFontNormal"])

	local EditBox = CreateFrame("EditBox", "TEXTBOX"..variable, LS.Tabs[tab].MiniTabs[minitab].Body, "InputBoxTemplate")
	EditBox:SetPoint("CENTER", LS.Tabs[tab].MiniTabs[minitab].Body, "TOPLEFT", LS.TextboxSizeX/2 + 15 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset,  -LS.TextboxSizeY -10 - LS.SpacingBetweenLines*line)
	EditBox:SetSize(LS.TextboxSizeX, LS.TextboxSizeY)
	EditBox:SetAutoFocus(false)
	EditBox:SetText(currentValue)
	EditBox:SetFontObject(_G["legendaryFontNormalAccentAlt"])

	local texture = EditBox:CreateTexture()
	texture:SetAllPoints()
	texture:SetPoint("TOPLEFT", EditBox ,"TOPLEFT", -4, 0)
	texture:SetPoint("BOTTOMRIGHT", EditBox ,"BOTTOMRIGHT", 0, 0)
	texture:SetTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Editbox")
	EditBox.texture = texture

	--Init value
	LS.Settings[variable] = currentValue

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls[#LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls + 1] = EditBox

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset + LS.ControlsSpacingX--7*#label +64

	--EditBox:HookScript("OnClick", function(self, button, down)
	--	LS.MinimizeDropdowns(nil)
	--end)
	EditBox:SetScript("OnTextChanged", function(self, value)
		LS.Settings[variable] = EditBox:GetText()
		LS.MinimizeDropdowns(nil)
	end)
end

-- Checkbox
function LS.AddCheckbox(tab, minitab, line, variable, label, default)

	LS.DefaultSettings[variable] = default

	local currentValue = default
	if LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile][variable] ~= nil then
		currentValue = LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile][variable]
	end

	if not LS.Tabs[tab].MiniTabs[minitab].Lines[line] then
		LS.Tabs[tab].MiniTabs[minitab].Lines[line] = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = 0
	end

	local frame=CreateFrame("Frame","CheckboxLabel"..variable,LS.Tabs[tab].MiniTabs[minitab].Body);
	frame:SetPoint("BOTTOM", LS.Tabs[tab].MiniTabs[minitab].Body, "TOPLEFT", 80 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset, -LS.CheckboxSize -10 - LS.SpacingBetweenLines*line)
	frame:SetSize(7*#label,LS.SettingControlHeight);

	local text=frame:CreateFontString(nil,"OVERLAY","GameFontNormal");
	text:SetPoint("CENTER");
	text:SetText(label);
	text:SetFontObject(_G["legendaryFontNormal"])

	local MyCheckbox = CreateFrame("CheckButton", "CHECKBOX"..variable, LS.Tabs[tab].MiniTabs[minitab].Body, "ChatConfigCheckButtonTemplate");
	MyCheckbox:SetSize(LS.CheckboxSize,LS.CheckboxSize);
	MyCheckbox:SetHitRectInsets(0,0,0,0)
	MyCheckbox:SetPoint("TOP", LS.Tabs[tab].MiniTabs[minitab].Body, "TOPLEFT", 80 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset, -LS.CheckboxSize - LS.SpacingBetweenLines*line)
	MyCheckbox:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Unchecked")
	MyCheckbox:SetPushedTexture("Interface\\Addons\\LegendarySettings\\Vectors\\Checked")
	MyCheckbox:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")

	--Init value
	MyCheckbox:SetChecked(currentValue)

	LS.Settings[variable] = currentValue

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls[#LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls + 1] = MyCheckbox

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset + LS.ControlsSpacingX--7*#label +64

	MyCheckbox:SetScript("OnClick", function(self, button, down)
		LS.Settings[variable] = self:GetChecked()
		LS.MinimizeDropdowns(nil)
	end)
end

-- Slider
function LS.AddSlider(tab, minitab, line, variable, label, min, max, default)

	LS.DefaultSettings[variable] = default

	local currentValue = LegendarySettingsDB[LS.SpecID].Profiles[LegendarySettingsDB[LS.SpecID].SelectedProfile][variable] or default

	if not LS.Tabs[tab].MiniTabs[minitab].Lines[line] then
		LS.Tabs[tab].MiniTabs[minitab].Lines[line] = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls = {}
		LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = 0
	end

	--local frame=CreateFrame("Frame","SliderLabel"..variable,LS.Tabs[tab].Body);
	--frame:SetPoint("TOPLEFT", LS.Tabs[tab].Body, "TOPLEFT", 10 + LS.Tabs[tab].Lines[line].NextOffset, -10 - LS.SpacingBetweenLines*line)
	--frame:SetSize(7*#label,LS.SettingControlHeight);
 
	--local text=frame:CreateFontString(nil,"OVERLAY","GameFontNormal");
	--text:SetPoint("TOPLEFT");
	--text:SetText(label);

	local MySlider = CreateFrame("Slider", "SLIDER"..variable, LS.Tabs[tab].MiniTabs[minitab].Body, "OptionsSliderTemplate")
	MySlider:SetWidth(LS.SliderWidth)
	MySlider:SetHeight(LS.SliderHeight)
	MySlider:SetPoint("LEFT", LS.Tabs[tab].MiniTabs[minitab].Body, "TOPLEFT", 10 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset, -LS.SettingControlHeight - LS.SpacingBetweenLines*line)
	MySlider:SetOrientation('HORIZONTAL')
	MySlider:SetMinMaxValues(min, max)
	MySlider:SetValue(currentValue)
	--MySlider:SetValueStep(1)
	--MySlider:SetStepsPerPage(1)
	MySlider:Show()

	MySlider:SetThumbTexture("Interface\\Addons\\LegendarySettings\\Vectors\\sliderThumb");

	local textureThumb = MySlider:GetThumbTexture()
	textureThumb:SetWidth(15)
	textureThumb:SetHeight(15)
	textureThumb:SetPoint("BOTTOM", 0, 1)


	local texture = MySlider:CreateTexture()
	texture:SetAllPoints()
	texture:SetPoint("TOPLEFT", MySlider ,"TOPLEFT", -2, 0)
	texture:SetPoint("BOTTOMRIGHT", MySlider ,"BOTTOMRIGHT", 0, -14)
	texture:SetTexture("Interface\\Addons\\LegendarySettings\\Vectors\\slider")
	MySlider.texture = texture

	--MySlider.tooltipText = 'This is the Tooltip hint'
	_G[MySlider:GetName() .. 'Low']:SetText(min)        -- Sets the left-side slider text (default is "Low").
	_G[MySlider:GetName() .. 'Low']:SetFontObject(_G["legendaryFontNormal"])
	_G[MySlider:GetName() .. 'High']:SetText(max)     -- Sets the right-side slider text (default is "High").
	_G[MySlider:GetName() .. 'High']:SetFontObject(_G["legendaryFontNormal"])
	_G[MySlider:GetName() .. 'Text']:SetText(label)       -- Sets the "title" text (top-centre of slider).
	_G[MySlider:GetName() .. 'Text']:SetFontObject(_G["legendaryFontNormal"])

	local frameValue =CreateFrame("Frame","SliderLabel"..variable,LS.Tabs[tab].MiniTabs[minitab].Body);
	frameValue:SetPoint("TOP", LS.Tabs[tab].MiniTabs[minitab].Body, "TOPLEFT", 10 + LS.SliderWidth/2 + LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset, -LS.SettingControlHeight - LS.SpacingBetweenLines*line)
	frameValue:SetSize(30 ,LS.SettingControlHeight);

	local textValue=frameValue:CreateFontString(nil,"OVERLAY","GameFontNormal");
	textValue:SetPoint("CENTER");
	textValue:SetText(currentValue);
	textValue:SetFontObject(_G["legendaryFontNormalAccent"])

	--Init value
	LS.Settings[variable] = currentValue

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls[#LS.Tabs[tab].MiniTabs[minitab].Lines[line].Controls + 1] = MySlider

	LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset = LS.Tabs[tab].MiniTabs[minitab].Lines[line].NextOffset + LS.ControlsSpacingX--+ 147 + LS.SliderWidth

	MySlider:SetScript("OnValueChanged", function(self, value)
		textValue:SetText(math.floor(value))
		LS.Settings[variable] = math.floor(value)
		LS.MinimizeDropdowns(nil)
	end)
end

-- Labels for Commands
function LS.AddLabelForCommands(minitab, line, label)
	if not LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line] then
		LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line] = {}
		LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line].Controls = {}
		LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line].NextOffset = 0
	end

	local frame=CreateFrame("Frame","TextboxLabel"..label,LS.SettingsFrameTabCommands.MiniTabs[minitab].Body);
	frame:SetPoint("LEFT", LS.SettingsFrameTabCommands.MiniTabs[minitab].Body, "TOPLEFT", 10 + LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line].NextOffset,  -30 - 14*line)
	frame:SetSize(7*#label,LS.SettingControlHeight);

	local text=frame:CreateFontString(nil,"OVERLAY","GameFontNormal");
	text:SetPoint("LEFT");
	text:SetText(label);
	text:SetFontObject(_G["legendaryFontAlternativeNormal"])

	LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line].Controls[#LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line].Controls + 1] = frame

	LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line].NextOffset = LS.SettingsFrameTabCommands.MiniTabs[minitab].Lines[line].NextOffset + 250--7*#label +64

	--EditBox:HookScript("OnClick", function(self, button, down)
	--	LS.MinimizeDropdowns(nil)
	--end)
end

function LS.AddCommandInfo(minitab, label)
	LS.SettingsFrameTabCommands.MiniTabs[minitab].NumberOfCommands = LS.SettingsFrameTabCommands.MiniTabs[minitab].NumberOfCommands + 1
	--LS.AddLabelForCommands(minitab, 3 + math.floor((LS.SettingsFrameTabCommands.MiniTabs[minitab].NumberOfCommands-1) / 3), label)
	LS.AddLabelForCommands(minitab, 3 + math.floor((LS.SettingsFrameTabCommands.MiniTabs[minitab].NumberOfCommands-1) % 38), label)
end

function LS.InitToggle(label, variable, default, explanation)
	local numberOfRegisteredToggles = 0

	LS.Toggles[string.lower(variable)] = default

	for k,v in pairs(LS.Toggles) do
		numberOfRegisteredToggles = numberOfRegisteredToggles+1;
	end

	if numberOfRegisteredToggles <= 15 then
		LS.Buttons[string.lower(variable)] = CreateFrame("Button", nil, FrameToggles, "UIPanelButtonTemplate")

		LS.Buttons[string.lower(variable)]:SetPoint("TOPLEFT", FrameToggles, "TOPLEFT", 3, -28 - 25*(numberOfRegisteredToggles-2))
		LS.Buttons[string.lower(variable)]:SetSize(83, 25)
		LS.Buttons[string.lower(variable)]:SetText(label);
		LS.Buttons[string.lower(variable)]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
		LS.Buttons[string.lower(variable)]:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		LS.Buttons[string.lower(variable)]:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		LS.Buttons[string.lower(variable)]:SetHighlightFontObject(_G["legendaryFontButtonSelected"])
		if LS.Toggles[string.lower(variable)] then
			LS.Buttons[string.lower(variable)]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton") -- 2ndtry
			LS.Buttons[string.lower(variable)]:SetNormalFontObject(_G["legendaryFontButtonSelected"])
		else
			LS.Buttons[string.lower(variable)]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
			LS.Buttons[string.lower(variable)]:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		end
		LS.Buttons[string.lower(variable)]:SetScript("OnClick", function(self, button, down)
			if LS.Toggles[string.lower(variable)] then
				LS.Toggles[string.lower(variable)] = false
				--self:SetText(label.." Off");
				LS.Buttons[string.lower(variable)]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
				LS.Buttons[string.lower(variable)]:SetNormalFontObject(_G["legendaryFontButtonNormal"])
			else
				LS.Toggles[string.lower(variable)] = true
				--self:SetText(label.." On");
				LS.Buttons[string.lower(variable)]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")  -- 2ndtry
				LS.Buttons[string.lower(variable)]:SetNormalFontObject(_G["legendaryFontButtonSelected"])
			end
		end)
		LS.Buttons[string.lower(variable)]:HookScript("OnMouseDown", function(self, button)
			FrameToggles:StartMoving()
		end)
		LS.Buttons[string.lower(variable)]:HookScript("OnMouseUp", function(self, button)
			FrameToggles:StopMovingOrSizing()
		end)
	end

	LS.AddLabelForCommands(1, 1+numberOfRegisteredToggles, explanation)
	LS.AddLabelForCommands(1, 1+numberOfRegisteredToggles, "/legendary "..variable)

	--Resize FrameToggles
	FrameToggles:SetHeight((numberOfRegisteredToggles+1)*25);
end

function LS.InitButtonMain(label, addonName)
	LS.Toggles["toggle"] = true

	if not LS.MainButton.Initialized then
		-- LS.MainButton.Initialized = true
		-- LS.MainButton.Name = label;
		-- LS.MainButton.Toggled = true
		-- ToggleButtonTop:SetText(label);
		-- ToggleButtonTop:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton") -- 2ndtry
		-- ToggleButtonTop:SetNormalFontObject(_G["legendaryFontButtonSelected"])
		-- ToggleButtonTop:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		-- ToggleButtonTop:SetHighlightFontObject(_G["legendaryFontButtonSelected"])
		-- ToggleButtonTop:Show();
		-- --ToggleButtonTop:SetAttribute("type1", "macro") -- left click causes macro
		-- --ToggleButtonTop:SetAttribute("macrotext1", "/"..addonName.." toggle")
		-- ToggleButtonTop:RegisterForClicks("RightButtonDown", "LeftButtonDown")
		-- ToggleButtonTop:HookScript("OnClick", ToggleButtonTop_OnClick)
		-- ToggleButtonTop:HookScript("OnMouseDown", function(self, button)
		-- 	FrameToggles:StartMoving()
		-- end)
		-- ToggleButtonTop:HookScript("OnMouseUp", function(self, button)
		-- 	FrameToggles:StopMovingOrSizing()
		-- end)

		--Hardcoded Toggle button
		LS.Buttons["toggle"] = CreateFrame("Button", nil, FrameToggles, "UIPanelButtonTemplate")

		LS.Buttons["toggle"]:SetPoint("TOPLEFT", FrameToggles, "TOPLEFT", 3, -3)
		LS.Buttons["toggle"]:SetSize(83, 25)
		LS.Buttons["toggle"]:SetText("Toggle");
		LS.Buttons["toggle"]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
		LS.Buttons["toggle"]:SetHighlightTexture("Interface\\Addons\\LegendarySettings\\Vectors\\White", "MOD")
		LS.Buttons["toggle"]:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		LS.Buttons["toggle"]:SetHighlightFontObject(_G["legendaryFontButtonSelected"])
		if LS.Toggles["toggle"] then
			LS.Buttons["toggle"]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton") -- 2ndtry
			LS.Buttons["toggle"]:SetNormalFontObject(_G["legendaryFontButtonSelected"])
		else
			LS.Buttons["toggle"]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
			LS.Buttons["toggle"]:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		end
		LS.Buttons["toggle"]:SetScript("OnClick", function(self, button, down)
			if LS.Toggles["toggle"] then
				LS.Toggles["toggle"] = false 
				--self:SetText(label.." Off");
				LS.Buttons["toggle"]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted") -- BigButtonS
				LS.Buttons["toggle"]:SetNormalFontObject(_G["legendaryFontButtonNormal"])
			else
				LS.Toggles["toggle"] = true
				--self:SetText(label.." On");
				LS.Buttons["toggle"]:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton")  -- 2ndtry
				LS.Buttons["toggle"]:SetNormalFontObject(_G["legendaryFontButtonSelected"])
			end
		end)
		LS.Buttons["toggle"]:HookScript("OnMouseDown", function(self, button)
			FrameToggles:StartMoving()
		end)
		LS.Buttons["toggle"]:HookScript("OnMouseUp", function(self, button)
			FrameToggles:StopMovingOrSizing()
		end)
	end
end

function LS.SetupVersion(version)
	LS.SettingsFrameTabProfiles.VersionText:SetText(version);
end

function SettingsButton_OnClick()
	--if not UnitAffectingCombat("player") then
		if not SettingsFrame:IsVisible() then
			SettingsFrame:Show();
		else
			SettingsFrame:Hide();
		end
	--end
end

function HideButton_OnClick()
	if not UnitAffectingCombat("player") then
		if not FrameToggles:IsVisible() then
			FrameToggles:Show();
		else
			FrameToggles:Hide();
		end
	end
end

function ToggleButtonTop_OnClick(self, args)
	if LS.MainButton.Toggled then
		LS.MainButton.Toggled = false
		--self:SetText(LS.MainButton.Name.." Off");
		self:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButtonNotHighlighted")
		self:SetNormalFontObject(_G["legendaryFontButtonNormal"])
		LS.Toggles["main"] = false
	else
		LS.MainButton.Toggled = true
		--self:SetText(LS.MainButton.Name.." On");
		self:SetNormalTexture("Interface\\Addons\\LegendarySettings\\Vectors\\BigButton") -- 2ndtry
		self:SetNormalFontObject(_G["legendaryFontButtonSelected"])
		LS.Toggles["main"] = true
	end
end

function ScrollFrame1_OnVerticalScroll()

end

function MiniButtons_OnDragStart(self, args)
	if self:IsMovable() then
		self:StartMoving()
	end
end

function MiniButtons_OnDragStop(self, args)
	if self:IsMovable() then
		self:StopMovingOrSizing()
	end
end


function LoadSaveButton_OnClick()
	--if not LS.SettingsFrameTabProfiles.Body:IsVisible() then
	--	LS.SettingsFrameTabProfiles.Body:Show();
	--else
	--	LS.SettingsFrameTabProfiles.Body:Hide();
	--end
	--for i,v in ipairs(LS.Tabs) do 
	--	v.Body:Hide();
	--end
	LS.ToggleTab(0, 0)
end

function CommandsButton_OnClick()
	LS.ToggleTab(99, 1)
end

function HideButton_OnDragStart()

end
