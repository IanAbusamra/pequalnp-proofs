import SplitCompact
namespace PetersenSigned.SixOpposite
private def pool1 : List (BitVec 156) := [68688647924508222385551503761514148542430445568,11799928204385924285541859289069053153202258047,48003935036336746740697505720551124557958873087,20093350251259722296534018426673980364679970688,68691479095237412483749153503022177030613467136,15381939137966892415745956730628625435006599168,75959079290926652971162858767545182698019487744]
private def case1_0 : List (BitVec 156) := [4719772413309517696,8070459328424706048]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_0 : case1_0.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_1 : List (BitVec 156) := [8070476920661082112,38960568283603750879232]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_1 : case1_1.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_2 : List (BitVec 156) := [226673591193681593892864,226673591212923047378944]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_2 : case1_2.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_3 : List (BitVec 156) := [302222231531620438900736,665932453551898437859898032111091712]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_3 : case1_3.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_4 : List (BitVec 156) := [2831170729190098197649741508028488183021568,2831171395122551749548178359120203763122176]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_4 : case1_4.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_5 : List (BitVec 156) := [724774262827397412859159242783960533464776704,1087161372641059899533163673733424067100278784]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_5 : case1_5.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_6 : List (BitVec 156) := [3584844837202922637743245174844921821272211456,3584844837868855131025622948721736481024917376]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_6 : case1_6.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_7 : List (BitVec 156) := [5798569763674949297567970196266047567164342272,5798572485933889780321225369778778996773650304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_7 : case1_7.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_8 : List (BitVec 156) := [7270431367084363039163253442882125871169142784,7270431367084363039163253443890932187700133888]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_8 : case1_8.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_9 : List (BitVec 156) := [8653065151745649609499447038328064423325745024,10855276204287285716636938994184487032863080320]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_9 : case1_9.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_10 : List (BitVec 156) := [11440285099514072687034571388345915941354225664,11797094300763969778002711555783703613734387712]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_10 : case1_10.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_11 : List (BitVec 156) := [11799928204385924285541859288488088798721212416,14294777765325832516212793056895201367906320384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_11 : case1_11.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_12 : List (BitVec 156) := [14294780487584772998966048230407932797515628416,14657164875139495002886797487844664901541822464]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_12 : case1_12.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_13 : List (BitVec 156) := [14659998778762747703560049927889834306103541760,15381939137966892415745654508397093814567698432]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_13 : case1_13.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_14 : List (BitVec 156) := [15381939137966892415745730057037412511959220224,15381939137966892415745730057037431753412706304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_14 : case1_14.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_15 : List (BitVec 156) := [20093350251259722296534018418603503444018888576,20093350251259722296534018418603521036255264640]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_15 : case1_15.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_16 : List (BitVec 156) := [20093350251259722296534018421954207951370452992,20500339032245453456239879674503581471233540096]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_16 : case1_16.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_17 : List (BitVec 156) := [20503170202974643554437529415435149207113039872,21180511623900782196067182100407404431780249472]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_17 : case1_17.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_18 : List (BitVec 156) := [22836747093870042092595266908781414963423870976,22839578264599232190792916649712982699303370752]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_18 : case1_18.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_19 : List (BitVec 156) := [23246567045584963350498777902262356219166457856,28679918518081937943472746396326729864433369088]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_19 : case1_19.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_20 : List (BitVec 156) := [28682752421705190644145998836371899268995088384,31539989092458761361490937035728475371815698432]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_20 : case1_20.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_21 : List (BitVec 156) := [43339917296844685647032796328936336583846428544,44064691559672083059891955567000524704001687552]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_21 : case1_21.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_22 : List (BitVec 156) := [45851900830638180292956236852732733579006574592,45851900830638180292956236853309194331310096384]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_22 : case1_22.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_23 : List (BitVec 156) := [47279160772844715027690112371218452833586118656,48003935036336746740697505719970160203477827456]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_23 : case1_23.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_24 : List (BitVec 156) := [68688647923842289931999605323654250510319353856,68688647923842289931999605324663056826850344960]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_24 : case1_24.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_25 : List (BitVec 156) := [68688647924508222385551277087922954860836552704,68688647924508222385551503753443689214005739520]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_25 : case1_25.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_26 : List (BitVec 156) := [68691479095237412483748926829430964107566088192,68691479095237412483749153494951700109952385024]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_26 : case1_26.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_27 : List (BitVec 156) := [70160509527251703673594888571279135130855145472,70890858977049858492688995717370571151967780864]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_27 : case1_27.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_28 : List (BitVec 156) := [75959079290926652971162556545313651077580587008,75959079290926652971162819806976899094268608512]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_28 : case1_28.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_29 : List (BitVec 156) := [75959079291592585424714757205405080730130579456,75959079291592585464445197580853713754021314432]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_29 : case1_29.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_30 : List (BitVec 156) := [75961910462321775522912406945904302901782609920,79543924128795508102188481716266919179044405120]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_30 : case1_30.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_31 : List (BitVec 156) := [79546755299524698200386092497206664063476547456,84070587062475114801297233818551580295843151872]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_31 : case1_31.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_32 : List (BitVec 156) := [84073418233204304899494883560059589542572687360,88781998175767944682085522180117669578685710208]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_32 : case1_32.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_33 : List (BitVec 156) := [88784829346497134780283171921625680474632355712,89191818127482865939989033176949297749543485440]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_33 : case1_33.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_34 : List (BitVec 156) := [89191818127482865939989033177525758501847007232,90253859778511425970128906997953115495535116160]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_34 : case1_34.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_35 : List (BitVec 156) := [90619078069689400674722908695435017004123029504,90984209228309580789223014144044551516647751552]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_35 : case1_35.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_36 : List (BitVec 156) := [91341018428893545386908513275942276512587186176,91341018429559477880191154311482339189027913600]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_36 : case1_36.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
private def case1_37 : List (BitVec 156) := [91343852333181432387730302044186724374014738304]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked_case1_37 : case1_37.all (fun v => !Compact.branch 78 6 pool1 302231454903657293676543 v) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem numeric1 : Compact.fast 78 7 pool1 302231454903657293676543 = false := by
  apply Compact.close_branches 78 6 pool1 302231454903657293676543 [case1_0,case1_1,case1_2,case1_3,case1_4,case1_5,case1_6,case1_7,case1_8,case1_9,case1_10,case1_11,case1_12,case1_13,case1_14,case1_15,case1_16,case1_17,case1_18,case1_19,case1_20,case1_21,case1_22,case1_23,case1_24,case1_25,case1_26,case1_27,case1_28,case1_29,case1_30,case1_31,case1_32,case1_33,case1_34,case1_35,case1_36,case1_37] (by decide +kernel) (by decide +kernel)
  intro bl hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked_case1_0
  · exact checked_case1_1
  · exact checked_case1_2
  · exact checked_case1_3
  · exact checked_case1_4
  · exact checked_case1_5
  · exact checked_case1_6
  · exact checked_case1_7
  · exact checked_case1_8
  · exact checked_case1_9
  · exact checked_case1_10
  · exact checked_case1_11
  · exact checked_case1_12
  · exact checked_case1_13
  · exact checked_case1_14
  · exact checked_case1_15
  · exact checked_case1_16
  · exact checked_case1_17
  · exact checked_case1_18
  · exact checked_case1_19
  · exact checked_case1_20
  · exact checked_case1_21
  · exact checked_case1_22
  · exact checked_case1_23
  · exact checked_case1_24
  · exact checked_case1_25
  · exact checked_case1_26
  · exact checked_case1_27
  · exact checked_case1_28
  · exact checked_case1_29
  · exact checked_case1_30
  · exact checked_case1_31
  · exact checked_case1_32
  · exact checked_case1_33
  · exact checked_case1_34
  · exact checked_case1_35
  · exact checked_case1_36
  · exact checked_case1_37
end PetersenSigned.SixOpposite
#print axioms PetersenSigned.SixOpposite.numeric1
