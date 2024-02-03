using Test

# using SoleLogics
# using SoleModels
using SoleRules
using StatsBase

# Letters making test suite

data = Dict(
    "Col1" => [
        [3.4879303918777853, 0.5059440378156133, 1.338977526291198, 0.8199127539313861, 3.4592518759299926, 0.6475430025347406, 3.0505708581395274, 1.5003376185686745, 3.8641759711602672, 4.450128256710112],
        [4.660283412051015, 2.817204043316337, 3.8203388469777053, 1.935979426872119, 4.258388473242819, 3.2342945434488817, 1.9168719741797307, 0.4643622152837157, 2.325711694672213, 1.2915085905832773],
        [1.7169837807749193, 0.06500191967989233, 3.434887882973026, 3.1838505006057023, 0.27209797401063607, 1.887170024975187, 1.2611316846613057, 0.6975900217496123, 4.945479391209236, 4.544026036576198],
        [3.9695473945704025, 1.110146355948184, 2.67142758775408, 3.1749726987318865, 3.0237700335043414, 3.334915745134868, 4.945577124326932, 4.570060206198639, 4.048886763683992, 3.9002361605462523],
        [0.9234433121807512, 0.4205053936922548, 2.4540727204541497, 3.7710435668576614, 2.497130406459704, 2.4259893534405523, 3.7752970322250685, 3.096849534927176, 4.643557892501975, 2.1355668802706633],
        [4.769758491299192, 3.1323034335605673, 1.9251088274938788, 4.358821998462683, 2.981756819940732, 0.6473022331421247, 1.8906600172010923, 4.112819547967007, 3.196215830140173, 1.2445687483421852],
        [0.5144930909417761, 3.2405797294867353, 1.9894898442065778, 1.7646044029847658, 3.3385131764903537, 2.996750560558088, 3.6091037471214276, 2.8023954094132986, 1.9803555136708857, 2.289150979141001],
        [1.2615275761318316, 3.505673811984324, 4.041062811931936, 1.1844617116436145, 1.9532400357400792, 0.8724554199284973, 2.393127909813864, 4.599936952039365, 3.4758167709863903, 0.13793813598579951],
        [2.5513688677366435, 4.504978510230021, 0.021585152256382578, 3.7268513256465208, 0.08690934100046066, 1.6065395369856321, 1.4584912154728902, 1.9539410282319785, 4.014408577549807, 2.534025820598975],
        [0.5709200675109971, 0.3423946881935319, 4.2693183514114095, 2.787430614274531, 1.4973290654875149, 0.8888825383060678, 1.7001780675753175, 4.789371502705916, 1.0351193849626479, 2.733908270030563],
    ],

    "Col2" => [
        [1.3677797456199126, 1.130765924136955, 5.771726653548982, 4.304839106271605, 0.20421655284520113, 6.056072351428769, 2.894493907438054, 8.05621953255997, 4.831340386591614, 3.1738367596744785],
        [4.460442249312332, 8.173039128995406, 6.986140555136044, 9.736824438583136, 0.12840043396214806, 6.4139320869655005, 2.8248318283227434, 5.597393727017397, 9.186084861728661, 7.851495300926969],
        [2.1571047766040294, 2.6157987354971945, 8.98460046981645, 5.22739688707114, 7.526988622571076, 3.1279874733836643, 9.372642479612836, 6.853887763741748, 5.895390268428607, 8.723919318304445],
        [1.1051353971058953, 9.525384451316064, 2.6894397830243655, 4.5453419516165585, 5.401978680798571, 0.5808323894840539, 8.638071286295556, 4.599753926564182, 6.365176382018925, 2.3115350731697704],
        [8.631080570498867, 4.892393830757372, 2.4834719234254132, 7.3780763733454835, 3.469743464301861, 9.994604771602846, 7.938886860647772, 1.717772245624699, 8.232072035973, 0.864255366503407],
        [8.461411763272853, 6.284200996979395, 5.850538579978504, 3.425983018971148, 8.93721188431886, 8.336633295536153, 2.426888938087534, 9.008137636249952, 2.9614683068428924, 4.66063535381962],
        [7.695876296967271, 4.603060354508363, 4.695470829844392, 4.062854874209725, 3.5117488919708206, 8.017959808615213, 0.3267603274939157, 3.024226885464122, 9.019890904548216, 8.075095468527454],
        [0.5714117528676477, 8.270645379126535, 8.169087474479047, 1.1043454042822098, 2.2238498335933454, 6.716889763955196, 6.273300293151144, 0.66739261620678, 1.2980210406473247, 8.143908423524092],
        [3.277200012176582, 8.150279995753317, 8.681479250933066, 7.117897090071464, 5.222457416622776, 4.615863968672064, 3.982840024954596, 3.6504700738958706, 3.654853278303931, 7.129292805266875],
        [3.2614893834143888, 7.326319222103709, 7.154247005095103, 0.6985347473352765, 5.143200936179021, 1.4075823732446036, 3.3150550852016036, 8.514840911518448, 0.05368807932236486, 5.665353978919608],
    ],

    "Col3" => [
        [-0.2527614616655658, 1.2309870403674994, 1.5620486831950577, -1.7316721531166397, -2.2701920413307812, -1.5167032273029304, -1.0155166415960666, -0.2598016701933221, 0.2955580903230972, -2.76636814846694],
        [0.6521402647749568, -0.10088120978102388, -1.063607913538996, 1.3282267521116777, 0.20147923469838735, -0.8191716368546378, -1.61147685166961, -2.653810925248476, -2.491717891387493, 1.23048499625052],
        [-1.407720301482016, -0.867686282199692, -0.9003687682266643, 1.0832259858351483, -0.10018089952017162, 1.307371754294965, -0.7076695773928994, 1.4277662789775167, 1.1943575745987278, 1.054597275972534],
        [0.36627878520269963, -2.564475391504581, -1.7639199965855707, 1.272993211915196, -1.5328294105102858, -0.42823509455339304, 1.027797775624303, -0.43587535680447864, 1.615588097962001, -0.039870402165842034],
        [-2.992388331999003, 0.4130371333911196, -1.8157492387087788, 0.7581225853801663, 0.42048215416794354, 0.44285422266248364, -1.0843847524919883, 0.784023073111694, -1.3874688567204703, -1.9229821288381532],
        [-1.5228151421196303, 1.8984428670278115, -2.2061069747592232, -1.0703541589975831, -2.0508589841506555, 1.256218363543411, 0.40505758563386074, 0.4393350858583922, -1.3754957203924651, -0.6368586003759704],
        [-2.65208541770105, 1.071802940072267, -2.2662952892861266, -2.8406972787953553, -1.954420772993088, 0.8780731771363679, -2.1301287374801605, 0.19560092728190792, 0.785718507701525, 1.4618563375836313],
        [-2.58987917279643, -2.2449992369821468, -1.0882252265735899, -0.5808678117566646, -1.3058860317057093, -0.6504099510625889, -1.4381549871505097, 0.9075130254922512, -2.4297897037193716, -2.1302245818056695],
        [-2.211565915573342, -1.8858308184246089, -1.8110120166720174, 1.4252415835366365, -2.3504720411816877, 0.9932198996731492, -1.2483900298870172, 0.9491781670155008, -1.4227698538744962, 0.13421337961174018],
        [-1.364085498371923, -0.06177122049443007, 1.441930801597863, 1.5584476220170913, -0.09136204798123826, -1.7983018295665132, -0.7501574355592977, -1.5475334531899771, -1.3864754678620301, -2.09414907324595],
    ],

    "Y[Hand tip l]" => [
        [0.36668931005657823, 0.8819873749028533, 0.24346306189403966, -0.11191021705598891, 0.18719723453155002, -0.937103130064723, -0.24084619659335837, -0.20847600570692038, 0.042088492382439835, 0.6883767337177316],
        [-0.2073308270479053, 0.7146093186140816, -0.5444105508740256, 0.046374854214753736, -0.32906751706345116, -0.08649016508601437, -0.08247047767436744, -0.6512745363146839, -0.639362025960349, 0.3455106629768918],
        [0.0638840992076759, 0.11623469332215564, -0.876032397651036, 0.3034720139366991, 0.9607789294824538, -0.7790432097321478, 0.5752594488629956, -0.305670336006729, -0.9908984614361775, 0.573980522585279],
        [-0.2595910393428118, 0.4027010463448448, -0.6580618251357053, -0.7818249453289057, 0.3089401330343129, 0.6498741422418395, -0.13054245347066185, 0.8438384419130072, 0.7297178522383103, -0.66260800283874],
        [-0.8706173682943428, 0.9761434796205235, 0.9949019420189058, 0.9373639374878326, -0.5905582042721191, -0.0713351668452209, -0.22434682361886038, 0.1838565575962925, -0.5181827433430224, 0.16768460560330967],
        [0.9465414066004081, -0.8699451097967774, 0.501195158438825, -0.8718717667893299, -0.2016215093659457, -0.5148436382530128, 0.4719618012540907, -0.5880884801067765, -0.7683058335349007, -0.46367830631764706],
        [-0.8989976566089042, 0.3553385983056139, -0.02404419273052638, 0.4766819150757733, -0.8858231834778558, 0.9656233890659611, 0.07266767219547554, 0.5153264168116565, 0.36778744630910665, 0.9664830455521629],
        [0.1108565713243106, -0.5771985453497641, -0.21025666180586144, 0.02540310897715381, -0.7118702703320492, -0.03732252457544516, -0.6798221129211783, 0.44422059659293534, 0.4381938171493429, -0.4217870387369793],
        [0.8173728069600772, 0.7545566144013494, 0.04112528716064534, -0.9270181201706666, 0.9686050276677121, -0.8621942563394338, 0.8330956620971828, 0.7076678623360466, 0.20627395745475008, -0.20804464443778214],
        [-0.0004604753747408097, 0.42932019614941885, 0.5049814492540361, 0.18896617840307184, 0.7722982872963007, -0.9054960374512298, -0.22002748670628747, -0.15118885906669988, -0.3244011870612238, -0.4567539165802361],
    ]
)

X_df = DataFrame(data)

@test equicut(X_df, minimum, 1, distance=2) == [0.021585152256382578, 0.06500191967989233, 0.3423946881935319, 0.4643622152837157, 0.5144930909417761, 1.110146355948184]
@test equicut(X_df, maximum, 1, distance=2) == [3.6091037471214276, 4.450128256710112, 4.599936952039365, 4.660283412051015, 4.789371502705916, 4.945577124326932]
@test equicut(X_df, mean, 1, distance=2) == [2.0614852550458496, 2.200821921721572, 2.31247722929593, 2.4525436454014913, 2.672494322062782, 3.4749540070399574]
@test equicut(X_df, minimum, 1, distance=2, keepleftbound=true) == [0.021585152256382578, 0.06500191967989233, 0.3423946881935319, 0.4643622152837157, 0.5144930909417761, 1.110146355948184]
@test equicut(X_df, maximum, 1, distance=2, keepleftbound=true) ==  [3.6091037471214276, 4.450128256710112, 4.599936952039365, 4.660283412051015, 4.789371502705916, 4.945577124326932]
@test equicut(X_df, mean, 1, distance=2, keepleftbound=true) == [2.0614852550458496, 2.200821921721572, 2.31247722929593, 2.4525436454014913, 2.672494322062782, 3.4749540070399574]

@test quantilecut(X_df, minimum, 1, nbins=3) == [0.0, 0.5, 1.0, 1.5]
@test quantilecut(X_df, maximum, 1, nbins=3) == [3.5, 4.0, 4.5, 5.0]
@test quantilecut(X_df, mean, 1, nbins=3) == [2.0, 2.5, 3.0, 3.5]

@test equicut(X_df, minimum, 2, distance=2) == [0.05368807932236486, 0.12840043396214806, 0.3267603274939157, 0.5808323894840539, 2.1571047766040294, 3.277200012176582]
@test equicut(X_df, maximum, 2, distance=2) == [8.05621953255997, 8.270645379126535, 8.681479250933066, 9.019890904548216, 9.525384451316064, 9.994604771602846]
@test equicut(X_df, mean, 2, distance=2) == [3.779129092011554, 4.254031172233413, 4.576264932139394, 5.5482633916650546, 6.0353109774056914, 6.135858461095034]
@test equicut(X_df, minimum, 2, distance=2, keepleftbound=true) == [0.05368807932236486, 0.12840043396214806, 0.3267603274939157, 0.5808323894840539, 2.1571047766040294, 3.277200012176582]
@test equicut(X_df, maximum, 2, distance=2, keepleftbound=true) == [8.05621953255997, 8.270645379126535, 8.681479250933066, 9.019890904548216, 9.525384451316064, 9.994604771602846]
@test equicut(X_df, mean, 2, distance=2, keepleftbound=true) == [3.779129092011554, 4.254031172233413, 4.576264932139394, 5.5482633916650546, 6.0353109774056914, 6.135858461095034]

@test quantilecut(X_df, minimum, 2, nbins=3) == [0.0, 1.0, 2.0, 3.0, 4.0]
@test quantilecut(X_df, maximum, 2, nbins=3) == [8.0, 9.0, 10.0]
@test quantilecut(X_df, mean, 2, nbins=3) == [3.0, 4.0, 5.0, 6.0, 7.0]
