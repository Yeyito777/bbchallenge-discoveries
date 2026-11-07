(** [halts_in tm c0 n_steps] for the holdout 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA, n_steps as in Statement.v. *)
From Coq Require Import ZArith.
From Coq Require Uint63.
From BusyCoq Require Import Individual62.
From BB6 Require Import Rules Map Num Vec Statement.
From BF Require HTop XTop.
From BF Require Import XFinal.
Require XCuts XJHalt.
Require XJ0000.
Require XJ0001.
Require XJ0002.
Require XJ0003.
Require XJ0004.
Require XJ0005.
Require XJ0006.
Require XJ0007.
Require XJ0008.
Require XJ0009.
Require XJ0010.
Require XJ0011.
Require XJ0012.
Require XJ0013.
Require XJ0014.
Require XJ0015.
Require XJ0016.
Require XJ0017.
Require XJ0018.
Require XJ0019.
Require XJ0020.
Require XJ0021.
Require XJ0022.
Require XJ0023.
Require XJ0024.
Require XJ0025.
Require XJ0026.
Require XJ0027.
Require XJ0028.
Require XJ0029.
Require XJ0030.
Require XJ0031.
Require XJ0032.
Require XJ0033.
Require XJ0034.
Require XJ0035.
Require XJ0036.
Require XJ0037.
Require XJ0038.
Require XJ0039.
Require XJ0040.
Require XJ0041.
Require XJ0042.
Require XJ0043.
Require XJ0044.
Require XJ0045.
Require XJ0046.
Require XJ0047.
Require XJ0048.
Require XJ0049.
Require XJ0050.
Require XJ0051.
Require XJ0052.
Require XJ0053.
Require XJ0054.
Require XJ0055.
Require XJ0056.
Require XJ0057.
Require XJ0058.
Require XJ0059.
Require XJ0060.
Require XJ0061.
Require XJ0062.
Require XJ0063.
Require XJ0064.
Require XJ0065.
Require XJ0066.
Require XJ0067.
Require XJ0068.
Require XJ0069.
Require XJ0070.
Require XJ0071.
Require XJ0072.
Require XJ0073.
Require XJ0074.
Require XJ0075.
Require XJ0076.
Require XJ0077.
Require XJ0078.
Require XJ0079.
Require XJ0080.
Require XJ0081.
Require XJ0082.
Require XJ0083.
Require XJ0084.
Require XJ0085.
Require XJ0086.
Require XJ0087.
Require XJ0088.
Require XJ0089.
Require XJ0090.
Require XJ0091.
Require XJ0092.
Require XJ0093.
Require XJ0094.
Require XJ0095.
Require XJ0096.
Require XJ0097.
Require XJ0098.
Require XJ0099.
Require XJ0100.
Require XJ0101.
Require XJ0102.
Require XJ0103.
Require XJ0104.
Require XJ0105.
Require XJ0106.
Require XJ0107.
Require XJ0108.
Require XJ0109.
Require XJ0110.
Require XJ0111.
Require XJ0112.
Require XJ0113.
Require XJ0114.
Require XJ0115.
Require XJ0116.
Require XJ0117.
Require XJ0118.
Require XJ0119.
Require XJ0120.
Require XJ0121.
Require XJ0122.
Require XJ0123.
Require XJ0124.
Require XJ0125.
Require XJ0126.
Require XJ0127.
Require XJ0128.
Require XJ0129.
Require XJ0130.
Require XJ0131.
Require XJ0132.
Require XJ0133.
Require XJ0134.
Require XJ0135.
Require XJ0136.
Require XJ0137.
Require XJ0138.
Require XJ0139.
Require XJ0140.
Require XJ0141.
Require XJ0142.
Require XJ0143.
Require XJ0144.
Require XJ0145.
Require XJ0146.
Require XJ0147.
Require XJ0148.
Require XJ0149.
Require XJ0150.
Require XJ0151.
Require XJ0152.
Require XJ0153.
Require XJ0154.
Require XJ0155.
Require XJ0156.
Require XJ0157.
Require XJ0158.
Require XJ0159.
Require XJ0160.
Require XJ0161.
Require XJ0162.
Require XJ0163.
Require XJ0164.
Require XJ0165.
Require XJ0166.
Require XJ0167.
Require XJ0168.
Require XJ0169.
Require XJ0170.
Require XJ0171.
Require XJ0172.
Require XJ0173.
Require XJ0174.
Require XJ0175.
Require XJ0176.
Require XJ0177.
Require XJ0178.
Require XJ0179.
Require XJ0180.
Require XJ0181.
Require XJ0182.
Require XJ0183.
Require XJ0184.
Require XJ0185.
Require XJ0186.
Require XJ0187.
Require XJ0188.
Require XJ0189.
Require XJ0190.
Require XJ0191.
Require XJ0192.
Require XJ0193.
Require XJ0194.
Require XJ0195.
Require XJ0196.
Require XJ0197.
Require XJ0198.
Require XJ0199.
Require XJ0200.
Require XJ0201.
Require XJ0202.
Require XJ0203.
Require XJ0204.
Require XJ0205.
Require XJ0206.
Require XJ0207.
Require XJ0208.
Require XJ0209.
Require XJ0210.
Require XJ0211.
Require XJ0212.
Require XJ0213.
Require XJ0214.
Require XJ0215.
Require XJ0216.
Require XJ0217.
Require XJ0218.
Require XJ0219.
Require XJ0220.
Require XJ0221.
Require XJ0222.
Require XJ0223.
Require XJ0224.
Require XJ0225.
Require XJ0226.
Require XJ0227.
Require XJ0228.
Require XJ0229.
Require XJ0230.
Require XJ0231.
Require XJ0232.
Require XJ0233.
Require XJ0234.
Require XJ0235.
Require XJ0236.
Require XJ0237.
Require XJ0238.
Require XJ0239.
Require XJ0240.
Require XJ0241.
Require XJ0242.
Require XJ0243.
Require XJ0244.
Require XJ0245.
Require XJ0246.
Require XJ0247.
Require XJ0248.
Require XJ0249.
Require XJ0250.
Require XJ0251.
Require XJ0252.
Require XJ0253.
Require XJ0254.
Require XJ0255.
Require XJ0256.
Require XJ0257.
Require XJ0258.
Require XJ0259.
Require XJ0260.
Require XJ0261.
Require XJ0262.
Require XJ0263.
Require XJ0264.
Require XJ0265.
Require XJ0266.
Require XJ0267.
Require XJ0268.
Require XJ0269.
Require XJ0270.
Require XJ0271.
Require XJ0272.
Require XJ0273.
Require XJ0274.
Require XJ0275.
Require XJ0276.
Require XJ0277.
Require XJ0278.
Require XJ0279.
Require XJ0280.
Require XJ0281.
Require XJ0282.
Require XJ0283.
Require XJ0284.
Require XJ0285.
Require XJ0286.
Require XJ0287.
Require XJ0288.
Require XJ0289.
Require XJ0290.
Require XJ0291.
Require XJ0292.
Require XJ0293.
Require XJ0294.
Require XJ0295.
Require XJ0296.
Require XJ0297.
Require XJ0298.
Require XJ0299.
Require XJ0300.
Require XJ0301.
Require XJ0302.
Require XJ0303.
Require XJ0304.
Require XJ0305.
Require XJ0306.
Require XJ0307.
Require XJ0308.
Require XJ0309.
Require XJ0310.
Require XJ0311.
Require XJ0312.
Require XJ0313.
Require XJ0314.
Require XJ0315.
Require XJ0316.
Require XJ0317.
Require XJ0318.
Require XJ0319.
Require XJ0320.
Require XJ0321.
Require XJ0322.
Require XJ0323.
Require XJ0324.
Require XJ0325.
Require XJ0326.
Require XJ0327.
Require XJ0328.
Require XJ0329.
Require XJ0330.
Require XJ0331.
Require XJ0332.
Require XJ0333.
Require XJ0334.
Require XJ0335.
Require XJ0336.
Require XJ0337.
Require XJ0338.
Require XJ0339.
Require XJ0340.
Require XJ0341.
Require XJ0342.
Require XJ0343.
Require XJ0344.
Require XJ0345.
Require XJ0346.
Require XJ0347.
Require XJ0348.
Require XJ0349.
Require XJ0350.
Require XJ0351.
Require XJ0352.
Require XJ0353.
Require XJ0354.
Require XJ0355.
Require XJ0356.
Require XJ0357.
Require XJ0358.
Require XJ0359.
Require XJ0360.
Require XJ0361.
Require XJ0362.
Require XJ0363.
Require XJ0364.
Require XJ0365.
Require XJ0366.
Require XJ0367.
Require XJ0368.
Require XJ0369.
Require XJ0370.
Require XJ0371.
Require XJ0372.
Require XJ0373.
Require XJ0374.
Require XJ0375.
Require XJ0376.
Require XJ0377.
Require XJ0378.
Require XJ0379.
Require XJ0380.
Require XJ0381.
Require XJ0382.
Require XJ0383.
Require XJ0384.
Require XJ0385.
Require XJ0386.
Require XJ0387.
Require XJ0388.
Require XJ0389.
Require XJ0390.
Require XJ0391.
Require XJ0392.
Require XJ0393.
Require XJ0394.
Require XJ0395.
Require XJ0396.
Require XJ0397.
Require XJ0398.
Require XJ0399.
Require XJ0400.
Require XJ0401.
Require XJ0402.
Require XJ0403.
Require XJ0404.
Require XJ0405.
Require XJ0406.
Require XJ0407.
Require XJ0408.
Require XJ0409.
Require XJ0410.
Require XJ0411.
Require XJ0412.
Require XJ0413.
Require XJ0414.
Require XJ0415.
Require XJ0416.
Require XJ0417.
Require XJ0418.
Require XJ0419.
Require XJ0420.
Require XJ0421.
Require XJ0422.
Require XJ0423.
Require XJ0424.
Require XJ0425.
Require XJ0426.
Require XJ0427.
Require XJ0428.
Require XJ0429.
Require XJ0430.
Require XJ0431.
Require XJ0432.
Require XJ0433.
Require XJ0434.
Require XJ0435.
Require XJ0436.
Require XJ0437.
Require XJ0438.
Require XJ0439.
Require XJ0440.
Require XJ0441.
Require XJ0442.
Require XJ0443.
Require XJ0444.
Require XJ0445.
Require XJ0446.
Require XJ0447.
Require XJ0448.
Require XJ0449.
Require XJ0450.
Require XJ0451.
Require XJ0452.
Require XJ0453.
Require XJ0454.
Require XJ0455.
Require XJ0456.
Require XJ0457.
Require XJ0458.
Require XJ0459.
Require XJ0460.
Require XJ0461.
Require XJ0462.
Require XJ0463.
Require XJ0464.
Require XJ0465.
Require XJ0466.
Require XJ0467.
Require XJ0468.
Require XJ0469.
Require XJ0470.
Require XJ0471.
Require XJ0472.
Require XJ0473.
Require XJ0474.
Require XJ0475.
Require XJ0476.
Require XJ0477.
Require XJ0478.
Require XJ0479.
Require XJ0480.
Require XJ0481.
Require XJ0482.
Require XJ0483.
Require XJ0484.
Require XJ0485.
Require XJ0486.
Require XJ0487.
Require XJ0488.
Require XJ0489.
Require XJ0490.
Require XJ0491.
Require XJ0492.
Require XJ0493.
Require XJ0494.
Require XJ0495.
Require XJ0496.
Require XJ0497.
Require XJ0498.
Require XJ0499.
Require XJ0500.
Require XJ0501.
Require XJ0502.
Require XJ0503.
Require XJ0504.
Require XJ0505.
Require XJ0506.
Require XJ0507.
Require XJ0508.
Require XJ0509.
Require XJ0510.
Require XJ0511.
Require XJ0512.
Require XJ0513.
Require XJ0514.
Require XJ0515.
Require XJ0516.
Require XJ0517.
Require XJ0518.
Require XJ0519.
Require XJ0520.
Require XJ0521.
Require XJ0522.
Require XJ0523.
Require XJ0524.
Require XJ0525.
Require XJ0526.
Require XJ0527.
Require XJ0528.
Require XJ0529.
Require XJ0530.
Require XJ0531.
Require XJ0532.
Require XJ0533.
Require XJ0534.
Require XJ0535.
Require XJ0536.
Require XJ0537.
Require XJ0538.
Require XJ0539.
Require XJ0540.
Require XJ0541.
Require XJ0542.
Require XJ0543.
Require XJ0544.
Require XJ0545.
Require XJ0546.
Require XJ0547.
Require XJ0548.
Require XJ0549.
Require XJ0550.
Require XJ0551.
Require XJ0552.
Require XJ0553.
Require XJ0554.
Require XJ0555.
Require XJ0556.
Require XJ0557.
Require XJ0558.
Require XJ0559.
Require XJ0560.
Require XJ0561.
Require XJ0562.
Require XJ0563.
Require XJ0564.
Require XJ0565.
Require XJ0566.
Require XJ0567.
Require XJ0568.
Require XJ0569.
Require XJ0570.
Require XJ0571.
Require XJ0572.
Require XJ0573.
Require XJ0574.
Require XJ0575.
Require XJ0576.
Require XJ0577.
Require XJ0578.
Require XJ0579.
Require XJ0580.
Require XJ0581.
Require XJ0582.
Require XJ0583.
Require XJ0584.
Require XJ0585.
Require XJ0586.
Require XJ0587.
Require XJ0588.
Require XJ0589.
Require XJ0590.
Require XJ0591.
Require XJ0592.
Require XJ0593.
Require XJ0594.
Require XJ0595.
Require XJ0596.
Require XJ0597.
Require XJ0598.
Require XJ0599.
Require XJ0600.
Require XJ0601.
Require XJ0602.
Require XJ0603.
Require XJ0604.
Require XJ0605.
Require XJ0606.
Require XJ0607.
Require XJ0608.
Require XJ0609.
Require XJ0610.
Require XJ0611.
Require XJ0612.
Require XJ0613.
Require XJ0614.
Require XJ0615.
Require XJ0616.
Require XJ0617.
Require XJ0618.
Require XJ0619.
Require XJ0620.
Require XJ0621.
Require XJ0622.
Require XJ0623.
Require XJ0624.
Require XJ0625.
Require XJ0626.
Require XJ0627.
Require XJ0628.
Require XJ0629.
Require XJ0630.
Require XJ0631.
Require XJ0632.
Require XJ0633.
Require XJ0634.
Require XJ0635.
Require XJ0636.
Require XJ0637.
Require XJ0638.
Require XJ0639.
Require XJ0640.
Require XJ0641.
Require XJ0642.
Require XJ0643.
Require XJ0644.
Require XJ0645.
Require XJ0646.
Require XJ0647.
Require XJ0648.
Require XJ0649.
Require XJ0650.
Require XJ0651.
Require XJ0652.
Require XJ0653.
Require XJ0654.
Require XJ0655.
Require XJ0656.
Require XJ0657.
Require XJ0658.
Require XJ0659.
Require XJ0660.
Require XJ0661.
Require XJ0662.
Require XJ0663.
Require XJ0664.
Require XJ0665.
Require XJ0666.
Require XJ0667.
Require XJ0668.
Require XJ0669.
Require XJ0670.
Require XJ0671.
Require XJ0672.
Require XJ0673.
Require XJ0674.
Require XJ0675.
Require XJ0676.
Require XJ0677.
Require XJ0678.
Require XJ0679.
Require XJ0680.
Require XJ0681.
Require XJ0682.
Require XJ0683.
Require XJ0684.
Require XJ0685.
Require XJ0686.
Require XJ0687.
Require XJ0688.
Require XJ0689.
Require XJ0690.
Require XJ0691.
Require XJ0692.
Require XJ0693.
Require XJ0694.
Require XJ0695.
Require XJ0696.
Require XJ0697.
Require XJ0698.
Require XJ0699.
Require XJ0700.
Require XJ0701.
Require XJ0702.
Require XJ0703.
Require XJ0704.
Require XJ0705.
Local Open Scope Z_scope.

Definition k0 := (XTop.xrun_seg_sound XCuts.z0 XCuts.b0 XCuts.z1 XCuts.b1 XCuts.n0 XCuts.v0 eq_refl XJ0000.seg).
Definition k1 := XR_trans _ _ _ _ _ _ _ _ _ _ k0 (XTop.xrun_seg_sound XCuts.z1 XCuts.b1 XCuts.z2 XCuts.b2 XCuts.n1 XCuts.v1 eq_refl XJ0001.seg).
Definition k2 := XR_trans _ _ _ _ _ _ _ _ _ _ k1 (XTop.xrun_seg_sound XCuts.z2 XCuts.b2 XCuts.z3 XCuts.b3 XCuts.n2 XCuts.v2 eq_refl XJ0002.seg).
Definition k3 := XR_trans _ _ _ _ _ _ _ _ _ _ k2 (XTop.xrun_seg_sound XCuts.z3 XCuts.b3 XCuts.z4 XCuts.b4 XCuts.n3 XCuts.v3 eq_refl XJ0003.seg).
Definition k4 := XR_trans _ _ _ _ _ _ _ _ _ _ k3 (XTop.xrun_seg_sound XCuts.z4 XCuts.b4 XCuts.z5 XCuts.b5 XCuts.n4 XCuts.v4 eq_refl XJ0004.seg).
Definition k5 := XR_trans _ _ _ _ _ _ _ _ _ _ k4 (XTop.xrun_seg_sound XCuts.z5 XCuts.b5 XCuts.z6 XCuts.b6 XCuts.n5 XCuts.v5 eq_refl XJ0005.seg).
Definition k6 := XR_trans _ _ _ _ _ _ _ _ _ _ k5 (XTop.xrun_seg_sound XCuts.z6 XCuts.b6 XCuts.z7 XCuts.b7 XCuts.n6 XCuts.v6 eq_refl XJ0006.seg).
Definition k7 := XR_trans _ _ _ _ _ _ _ _ _ _ k6 (XTop.xrun_seg_sound XCuts.z7 XCuts.b7 XCuts.z8 XCuts.b8 XCuts.n7 XCuts.v7 eq_refl XJ0007.seg).
Definition k8 := XR_trans _ _ _ _ _ _ _ _ _ _ k7 (XTop.xrun_seg_sound XCuts.z8 XCuts.b8 XCuts.z9 XCuts.b9 XCuts.n8 XCuts.v8 eq_refl XJ0008.seg).
Definition k9 := XR_trans _ _ _ _ _ _ _ _ _ _ k8 (XTop.xrun_seg_sound XCuts.z9 XCuts.b9 XCuts.z10 XCuts.b10 XCuts.n9 XCuts.v9 eq_refl XJ0009.seg).
Definition k10 := XR_trans _ _ _ _ _ _ _ _ _ _ k9 (XTop.xrun_seg_sound XCuts.z10 XCuts.b10 XCuts.z11 XCuts.b11 XCuts.n10 XCuts.v10 eq_refl XJ0010.seg).
Definition k11 := XR_trans _ _ _ _ _ _ _ _ _ _ k10 (XTop.xrun_seg_sound XCuts.z11 XCuts.b11 XCuts.z12 XCuts.b12 XCuts.n11 XCuts.v11 eq_refl XJ0011.seg).
Definition k12 := XR_trans _ _ _ _ _ _ _ _ _ _ k11 (XTop.xrun_seg_sound XCuts.z12 XCuts.b12 XCuts.z13 XCuts.b13 XCuts.n12 XCuts.v12 eq_refl XJ0012.seg).
Definition k13 := XR_trans _ _ _ _ _ _ _ _ _ _ k12 (XTop.xrun_seg_sound XCuts.z13 XCuts.b13 XCuts.z14 XCuts.b14 XCuts.n13 XCuts.v13 eq_refl XJ0013.seg).
Definition k14 := XR_trans _ _ _ _ _ _ _ _ _ _ k13 (XTop.xrun_seg_sound XCuts.z14 XCuts.b14 XCuts.z15 XCuts.b15 XCuts.n14 XCuts.v14 eq_refl XJ0014.seg).
Definition k15 := XR_trans _ _ _ _ _ _ _ _ _ _ k14 (XTop.xrun_seg_sound XCuts.z15 XCuts.b15 XCuts.z16 XCuts.b16 XCuts.n15 XCuts.v15 eq_refl XJ0015.seg).
Definition k16 := XR_trans _ _ _ _ _ _ _ _ _ _ k15 (XTop.xrun_seg_sound XCuts.z16 XCuts.b16 XCuts.z17 XCuts.b17 XCuts.n16 XCuts.v16 eq_refl XJ0016.seg).
Definition k17 := XR_trans _ _ _ _ _ _ _ _ _ _ k16 (XTop.xrun_seg_sound XCuts.z17 XCuts.b17 XCuts.z18 XCuts.b18 XCuts.n17 XCuts.v17 eq_refl XJ0017.seg).
Definition k18 := XR_trans _ _ _ _ _ _ _ _ _ _ k17 (XTop.xrun_seg_sound XCuts.z18 XCuts.b18 XCuts.z19 XCuts.b19 XCuts.n18 XCuts.v18 eq_refl XJ0018.seg).
Definition k19 := XR_trans _ _ _ _ _ _ _ _ _ _ k18 (XTop.xrun_seg_sound XCuts.z19 XCuts.b19 XCuts.z20 XCuts.b20 XCuts.n19 XCuts.v19 eq_refl XJ0019.seg).
Definition k20 := XR_trans _ _ _ _ _ _ _ _ _ _ k19 (XTop.xrun_seg_sound XCuts.z20 XCuts.b20 XCuts.z21 XCuts.b21 XCuts.n20 XCuts.v20 eq_refl XJ0020.seg).
Definition k21 := XR_trans _ _ _ _ _ _ _ _ _ _ k20 (XTop.xrun_seg_sound XCuts.z21 XCuts.b21 XCuts.z22 XCuts.b22 XCuts.n21 XCuts.v21 eq_refl XJ0021.seg).
Definition k22 := XR_trans _ _ _ _ _ _ _ _ _ _ k21 (XTop.xrun_seg_sound XCuts.z22 XCuts.b22 XCuts.z23 XCuts.b23 XCuts.n22 XCuts.v22 eq_refl XJ0022.seg).
Definition k23 := XR_trans _ _ _ _ _ _ _ _ _ _ k22 (XTop.xrun_seg_sound XCuts.z23 XCuts.b23 XCuts.z24 XCuts.b24 XCuts.n23 XCuts.v23 eq_refl XJ0023.seg).
Definition k24 := XR_trans _ _ _ _ _ _ _ _ _ _ k23 (XTop.xrun_seg_sound XCuts.z24 XCuts.b24 XCuts.z25 XCuts.b25 XCuts.n24 XCuts.v24 eq_refl XJ0024.seg).
Definition k25 := XR_trans _ _ _ _ _ _ _ _ _ _ k24 (XTop.xrun_seg_sound XCuts.z25 XCuts.b25 XCuts.z26 XCuts.b26 XCuts.n25 XCuts.v25 eq_refl XJ0025.seg).
Definition k26 := XR_trans _ _ _ _ _ _ _ _ _ _ k25 (XTop.xrun_seg_sound XCuts.z26 XCuts.b26 XCuts.z27 XCuts.b27 XCuts.n26 XCuts.v26 eq_refl XJ0026.seg).
Definition k27 := XR_trans _ _ _ _ _ _ _ _ _ _ k26 (XTop.xrun_seg_sound XCuts.z27 XCuts.b27 XCuts.z28 XCuts.b28 XCuts.n27 XCuts.v27 eq_refl XJ0027.seg).
Definition k28 := XR_trans _ _ _ _ _ _ _ _ _ _ k27 (XTop.xrun_seg_sound XCuts.z28 XCuts.b28 XCuts.z29 XCuts.b29 XCuts.n28 XCuts.v28 eq_refl XJ0028.seg).
Definition k29 := XR_trans _ _ _ _ _ _ _ _ _ _ k28 (XTop.xrun_seg_sound XCuts.z29 XCuts.b29 XCuts.z30 XCuts.b30 XCuts.n29 XCuts.v29 eq_refl XJ0029.seg).
Definition k30 := XR_trans _ _ _ _ _ _ _ _ _ _ k29 (XTop.xrun_seg_sound XCuts.z30 XCuts.b30 XCuts.z31 XCuts.b31 XCuts.n30 XCuts.v30 eq_refl XJ0030.seg).
Definition k31 := XR_trans _ _ _ _ _ _ _ _ _ _ k30 (XTop.xrun_seg_sound XCuts.z31 XCuts.b31 XCuts.z32 XCuts.b32 XCuts.n31 XCuts.v31 eq_refl XJ0031.seg).
Definition k32 := XR_trans _ _ _ _ _ _ _ _ _ _ k31 (XTop.xrun_seg_sound XCuts.z32 XCuts.b32 XCuts.z33 XCuts.b33 XCuts.n32 XCuts.v32 eq_refl XJ0032.seg).
Definition k33 := XR_trans _ _ _ _ _ _ _ _ _ _ k32 (XTop.xrun_seg_sound XCuts.z33 XCuts.b33 XCuts.z34 XCuts.b34 XCuts.n33 XCuts.v33 eq_refl XJ0033.seg).
Definition k34 := XR_trans _ _ _ _ _ _ _ _ _ _ k33 (XTop.xrun_seg_sound XCuts.z34 XCuts.b34 XCuts.z35 XCuts.b35 XCuts.n34 XCuts.v34 eq_refl XJ0034.seg).
Definition k35 := XR_trans _ _ _ _ _ _ _ _ _ _ k34 (XTop.xrun_seg_sound XCuts.z35 XCuts.b35 XCuts.z36 XCuts.b36 XCuts.n35 XCuts.v35 eq_refl XJ0035.seg).
Definition k36 := XR_trans _ _ _ _ _ _ _ _ _ _ k35 (XTop.xrun_seg_sound XCuts.z36 XCuts.b36 XCuts.z37 XCuts.b37 XCuts.n36 XCuts.v36 eq_refl XJ0036.seg).
Definition k37 := XR_trans _ _ _ _ _ _ _ _ _ _ k36 (XTop.xrun_seg_sound XCuts.z37 XCuts.b37 XCuts.z38 XCuts.b38 XCuts.n37 XCuts.v37 eq_refl XJ0037.seg).
Definition k38 := XR_trans _ _ _ _ _ _ _ _ _ _ k37 (XTop.xrun_seg_sound XCuts.z38 XCuts.b38 XCuts.z39 XCuts.b39 XCuts.n38 XCuts.v38 eq_refl XJ0038.seg).
Definition k39 := XR_trans _ _ _ _ _ _ _ _ _ _ k38 (XTop.xrun_seg_sound XCuts.z39 XCuts.b39 XCuts.z40 XCuts.b40 XCuts.n39 XCuts.v39 eq_refl XJ0039.seg).
Definition k40 := XR_trans _ _ _ _ _ _ _ _ _ _ k39 (XTop.xrun_seg_sound XCuts.z40 XCuts.b40 XCuts.z41 XCuts.b41 XCuts.n40 XCuts.v40 eq_refl XJ0040.seg).
Definition k41 := XR_trans _ _ _ _ _ _ _ _ _ _ k40 (XTop.xrun_seg_sound XCuts.z41 XCuts.b41 XCuts.z42 XCuts.b42 XCuts.n41 XCuts.v41 eq_refl XJ0041.seg).
Definition k42 := XR_trans _ _ _ _ _ _ _ _ _ _ k41 (XTop.xrun_seg_sound XCuts.z42 XCuts.b42 XCuts.z43 XCuts.b43 XCuts.n42 XCuts.v42 eq_refl XJ0042.seg).
Definition k43 := XR_trans _ _ _ _ _ _ _ _ _ _ k42 (XTop.xrun_seg_sound XCuts.z43 XCuts.b43 XCuts.z44 XCuts.b44 XCuts.n43 XCuts.v43 eq_refl XJ0043.seg).
Definition k44 := XR_trans _ _ _ _ _ _ _ _ _ _ k43 (XTop.xrun_seg_sound XCuts.z44 XCuts.b44 XCuts.z45 XCuts.b45 XCuts.n44 XCuts.v44 eq_refl XJ0044.seg).
Definition k45 := XR_trans _ _ _ _ _ _ _ _ _ _ k44 (XTop.xrun_seg_sound XCuts.z45 XCuts.b45 XCuts.z46 XCuts.b46 XCuts.n45 XCuts.v45 eq_refl XJ0045.seg).
Definition k46 := XR_trans _ _ _ _ _ _ _ _ _ _ k45 (XTop.xrun_seg_sound XCuts.z46 XCuts.b46 XCuts.z47 XCuts.b47 XCuts.n46 XCuts.v46 eq_refl XJ0046.seg).
Definition k47 := XR_trans _ _ _ _ _ _ _ _ _ _ k46 (XTop.xrun_seg_sound XCuts.z47 XCuts.b47 XCuts.z48 XCuts.b48 XCuts.n47 XCuts.v47 eq_refl XJ0047.seg).
Definition k48 := XR_trans _ _ _ _ _ _ _ _ _ _ k47 (XTop.xrun_seg_sound XCuts.z48 XCuts.b48 XCuts.z49 XCuts.b49 XCuts.n48 XCuts.v48 eq_refl XJ0048.seg).
Definition k49 := XR_trans _ _ _ _ _ _ _ _ _ _ k48 (XTop.xrun_seg_sound XCuts.z49 XCuts.b49 XCuts.z50 XCuts.b50 XCuts.n49 XCuts.v49 eq_refl XJ0049.seg).
Definition k50 := XR_trans _ _ _ _ _ _ _ _ _ _ k49 (XTop.xrun_seg_sound XCuts.z50 XCuts.b50 XCuts.z51 XCuts.b51 XCuts.n50 XCuts.v50 eq_refl XJ0050.seg).
Definition k51 := XR_trans _ _ _ _ _ _ _ _ _ _ k50 (XTop.xrun_seg_sound XCuts.z51 XCuts.b51 XCuts.z52 XCuts.b52 XCuts.n51 XCuts.v51 eq_refl XJ0051.seg).
Definition k52 := XR_trans _ _ _ _ _ _ _ _ _ _ k51 (XTop.xrun_seg_sound XCuts.z52 XCuts.b52 XCuts.z53 XCuts.b53 XCuts.n52 XCuts.v52 eq_refl XJ0052.seg).
Definition k53 := XR_trans _ _ _ _ _ _ _ _ _ _ k52 (XTop.xrun_seg_sound XCuts.z53 XCuts.b53 XCuts.z54 XCuts.b54 XCuts.n53 XCuts.v53 eq_refl XJ0053.seg).
Definition k54 := XR_trans _ _ _ _ _ _ _ _ _ _ k53 (XTop.xrun_seg_sound XCuts.z54 XCuts.b54 XCuts.z55 XCuts.b55 XCuts.n54 XCuts.v54 eq_refl XJ0054.seg).
Definition k55 := XR_trans _ _ _ _ _ _ _ _ _ _ k54 (XTop.xrun_seg_sound XCuts.z55 XCuts.b55 XCuts.z56 XCuts.b56 XCuts.n55 XCuts.v55 eq_refl XJ0055.seg).
Definition k56 := XR_trans _ _ _ _ _ _ _ _ _ _ k55 (XTop.xrun_seg_sound XCuts.z56 XCuts.b56 XCuts.z57 XCuts.b57 XCuts.n56 XCuts.v56 eq_refl XJ0056.seg).
Definition k57 := XR_trans _ _ _ _ _ _ _ _ _ _ k56 (XTop.xrun_seg_sound XCuts.z57 XCuts.b57 XCuts.z58 XCuts.b58 XCuts.n57 XCuts.v57 eq_refl XJ0057.seg).
Definition k58 := XR_trans _ _ _ _ _ _ _ _ _ _ k57 (XTop.xrun_seg_sound XCuts.z58 XCuts.b58 XCuts.z59 XCuts.b59 XCuts.n58 XCuts.v58 eq_refl XJ0058.seg).
Definition k59 := XR_trans _ _ _ _ _ _ _ _ _ _ k58 (XTop.xrun_seg_sound XCuts.z59 XCuts.b59 XCuts.z60 XCuts.b60 XCuts.n59 XCuts.v59 eq_refl XJ0059.seg).
Definition k60 := XR_trans _ _ _ _ _ _ _ _ _ _ k59 (XTop.xrun_seg_sound XCuts.z60 XCuts.b60 XCuts.z61 XCuts.b61 XCuts.n60 XCuts.v60 eq_refl XJ0060.seg).
Definition k61 := XR_trans _ _ _ _ _ _ _ _ _ _ k60 (XTop.xrun_seg_sound XCuts.z61 XCuts.b61 XCuts.z62 XCuts.b62 XCuts.n61 XCuts.v61 eq_refl XJ0061.seg).
Definition k62 := XR_trans _ _ _ _ _ _ _ _ _ _ k61 (XTop.xrun_seg_sound XCuts.z62 XCuts.b62 XCuts.z63 XCuts.b63 XCuts.n62 XCuts.v62 eq_refl XJ0062.seg).
Definition k63 := XR_trans _ _ _ _ _ _ _ _ _ _ k62 (XTop.xrun_seg_sound XCuts.z63 XCuts.b63 XCuts.z64 XCuts.b64 XCuts.n63 XCuts.v63 eq_refl XJ0063.seg).
Definition k64 := XR_trans _ _ _ _ _ _ _ _ _ _ k63 (XTop.xrun_seg_sound XCuts.z64 XCuts.b64 XCuts.z65 XCuts.b65 XCuts.n64 XCuts.v64 eq_refl XJ0064.seg).
Definition k65 := XR_trans _ _ _ _ _ _ _ _ _ _ k64 (XTop.xrun_seg_sound XCuts.z65 XCuts.b65 XCuts.z66 XCuts.b66 XCuts.n65 XCuts.v65 eq_refl XJ0065.seg).
Definition k66 := XR_trans _ _ _ _ _ _ _ _ _ _ k65 (XTop.xrun_seg_sound XCuts.z66 XCuts.b66 XCuts.z67 XCuts.b67 XCuts.n66 XCuts.v66 eq_refl XJ0066.seg).
Definition k67 := XR_trans _ _ _ _ _ _ _ _ _ _ k66 (XTop.xrun_seg_sound XCuts.z67 XCuts.b67 XCuts.z68 XCuts.b68 XCuts.n67 XCuts.v67 eq_refl XJ0067.seg).
Definition k68 := XR_trans _ _ _ _ _ _ _ _ _ _ k67 (XTop.xrun_seg_sound XCuts.z68 XCuts.b68 XCuts.z69 XCuts.b69 XCuts.n68 XCuts.v68 eq_refl XJ0068.seg).
Definition k69 := XR_trans _ _ _ _ _ _ _ _ _ _ k68 (XTop.xrun_seg_sound XCuts.z69 XCuts.b69 XCuts.z70 XCuts.b70 XCuts.n69 XCuts.v69 eq_refl XJ0069.seg).
Definition k70 := XR_trans _ _ _ _ _ _ _ _ _ _ k69 (XTop.xrun_seg_sound XCuts.z70 XCuts.b70 XCuts.z71 XCuts.b71 XCuts.n70 XCuts.v70 eq_refl XJ0070.seg).
Definition k71 := XR_trans _ _ _ _ _ _ _ _ _ _ k70 (XTop.xrun_seg_sound XCuts.z71 XCuts.b71 XCuts.z72 XCuts.b72 XCuts.n71 XCuts.v71 eq_refl XJ0071.seg).
Definition k72 := XR_trans _ _ _ _ _ _ _ _ _ _ k71 (XTop.xrun_seg_sound XCuts.z72 XCuts.b72 XCuts.z73 XCuts.b73 XCuts.n72 XCuts.v72 eq_refl XJ0072.seg).
Definition k73 := XR_trans _ _ _ _ _ _ _ _ _ _ k72 (XTop.xrun_seg_sound XCuts.z73 XCuts.b73 XCuts.z74 XCuts.b74 XCuts.n73 XCuts.v73 eq_refl XJ0073.seg).
Definition k74 := XR_trans _ _ _ _ _ _ _ _ _ _ k73 (XTop.xrun_seg_sound XCuts.z74 XCuts.b74 XCuts.z75 XCuts.b75 XCuts.n74 XCuts.v74 eq_refl XJ0074.seg).
Definition k75 := XR_trans _ _ _ _ _ _ _ _ _ _ k74 (XTop.xrun_seg_sound XCuts.z75 XCuts.b75 XCuts.z76 XCuts.b76 XCuts.n75 XCuts.v75 eq_refl XJ0075.seg).
Definition k76 := XR_trans _ _ _ _ _ _ _ _ _ _ k75 (XTop.xrun_seg_sound XCuts.z76 XCuts.b76 XCuts.z77 XCuts.b77 XCuts.n76 XCuts.v76 eq_refl XJ0076.seg).
Definition k77 := XR_trans _ _ _ _ _ _ _ _ _ _ k76 (XTop.xrun_seg_sound XCuts.z77 XCuts.b77 XCuts.z78 XCuts.b78 XCuts.n77 XCuts.v77 eq_refl XJ0077.seg).
Definition k78 := XR_trans _ _ _ _ _ _ _ _ _ _ k77 (XTop.xrun_seg_sound XCuts.z78 XCuts.b78 XCuts.z79 XCuts.b79 XCuts.n78 XCuts.v78 eq_refl XJ0078.seg).
Definition k79 := XR_trans _ _ _ _ _ _ _ _ _ _ k78 (XTop.xrun_seg_sound XCuts.z79 XCuts.b79 XCuts.z80 XCuts.b80 XCuts.n79 XCuts.v79 eq_refl XJ0079.seg).
Definition k80 := XR_trans _ _ _ _ _ _ _ _ _ _ k79 (XTop.xrun_seg_sound XCuts.z80 XCuts.b80 XCuts.z81 XCuts.b81 XCuts.n80 XCuts.v80 eq_refl XJ0080.seg).
Definition k81 := XR_trans _ _ _ _ _ _ _ _ _ _ k80 (XTop.xrun_seg_sound XCuts.z81 XCuts.b81 XCuts.z82 XCuts.b82 XCuts.n81 XCuts.v81 eq_refl XJ0081.seg).
Definition k82 := XR_trans _ _ _ _ _ _ _ _ _ _ k81 (XTop.xrun_seg_sound XCuts.z82 XCuts.b82 XCuts.z83 XCuts.b83 XCuts.n82 XCuts.v82 eq_refl XJ0082.seg).
Definition k83 := XR_trans _ _ _ _ _ _ _ _ _ _ k82 (XTop.xrun_seg_sound XCuts.z83 XCuts.b83 XCuts.z84 XCuts.b84 XCuts.n83 XCuts.v83 eq_refl XJ0083.seg).
Definition k84 := XR_trans _ _ _ _ _ _ _ _ _ _ k83 (XTop.xrun_seg_sound XCuts.z84 XCuts.b84 XCuts.z85 XCuts.b85 XCuts.n84 XCuts.v84 eq_refl XJ0084.seg).
Definition k85 := XR_trans _ _ _ _ _ _ _ _ _ _ k84 (XTop.xrun_seg_sound XCuts.z85 XCuts.b85 XCuts.z86 XCuts.b86 XCuts.n85 XCuts.v85 eq_refl XJ0085.seg).
Definition k86 := XR_trans _ _ _ _ _ _ _ _ _ _ k85 (XTop.xrun_seg_sound XCuts.z86 XCuts.b86 XCuts.z87 XCuts.b87 XCuts.n86 XCuts.v86 eq_refl XJ0086.seg).
Definition k87 := XR_trans _ _ _ _ _ _ _ _ _ _ k86 (XTop.xrun_seg_sound XCuts.z87 XCuts.b87 XCuts.z88 XCuts.b88 XCuts.n87 XCuts.v87 eq_refl XJ0087.seg).
Definition k88 := XR_trans _ _ _ _ _ _ _ _ _ _ k87 (XTop.xrun_seg_sound XCuts.z88 XCuts.b88 XCuts.z89 XCuts.b89 XCuts.n88 XCuts.v88 eq_refl XJ0088.seg).
Definition k89 := XR_trans _ _ _ _ _ _ _ _ _ _ k88 (XTop.xrun_seg_sound XCuts.z89 XCuts.b89 XCuts.z90 XCuts.b90 XCuts.n89 XCuts.v89 eq_refl XJ0089.seg).
Definition k90 := XR_trans _ _ _ _ _ _ _ _ _ _ k89 (XTop.xrun_seg_sound XCuts.z90 XCuts.b90 XCuts.z91 XCuts.b91 XCuts.n90 XCuts.v90 eq_refl XJ0090.seg).
Definition k91 := XR_trans _ _ _ _ _ _ _ _ _ _ k90 (XTop.xrun_seg_sound XCuts.z91 XCuts.b91 XCuts.z92 XCuts.b92 XCuts.n91 XCuts.v91 eq_refl XJ0091.seg).
Definition k92 := XR_trans _ _ _ _ _ _ _ _ _ _ k91 (XTop.xrun_seg_sound XCuts.z92 XCuts.b92 XCuts.z93 XCuts.b93 XCuts.n92 XCuts.v92 eq_refl XJ0092.seg).
Definition k93 := XR_trans _ _ _ _ _ _ _ _ _ _ k92 (XTop.xrun_seg_sound XCuts.z93 XCuts.b93 XCuts.z94 XCuts.b94 XCuts.n93 XCuts.v93 eq_refl XJ0093.seg).
Definition k94 := XR_trans _ _ _ _ _ _ _ _ _ _ k93 (XTop.xrun_seg_sound XCuts.z94 XCuts.b94 XCuts.z95 XCuts.b95 XCuts.n94 XCuts.v94 eq_refl XJ0094.seg).
Definition k95 := XR_trans _ _ _ _ _ _ _ _ _ _ k94 (XTop.xrun_seg_sound XCuts.z95 XCuts.b95 XCuts.z96 XCuts.b96 XCuts.n95 XCuts.v95 eq_refl XJ0095.seg).
Definition k96 := XR_trans _ _ _ _ _ _ _ _ _ _ k95 (XTop.xrun_seg_sound XCuts.z96 XCuts.b96 XCuts.z97 XCuts.b97 XCuts.n96 XCuts.v96 eq_refl XJ0096.seg).
Definition k97 := XR_trans _ _ _ _ _ _ _ _ _ _ k96 (XTop.xrun_seg_sound XCuts.z97 XCuts.b97 XCuts.z98 XCuts.b98 XCuts.n97 XCuts.v97 eq_refl XJ0097.seg).
Definition k98 := XR_trans _ _ _ _ _ _ _ _ _ _ k97 (XTop.xrun_seg_sound XCuts.z98 XCuts.b98 XCuts.z99 XCuts.b99 XCuts.n98 XCuts.v98 eq_refl XJ0098.seg).
Definition k99 := XR_trans _ _ _ _ _ _ _ _ _ _ k98 (XTop.xrun_seg_sound XCuts.z99 XCuts.b99 XCuts.z100 XCuts.b100 XCuts.n99 XCuts.v99 eq_refl XJ0099.seg).
Definition k100 := XR_trans _ _ _ _ _ _ _ _ _ _ k99 (XTop.xrun_seg_sound XCuts.z100 XCuts.b100 XCuts.z101 XCuts.b101 XCuts.n100 XCuts.v100 eq_refl XJ0100.seg).
Definition k101 := XR_trans _ _ _ _ _ _ _ _ _ _ k100 (XTop.xrun_seg_sound XCuts.z101 XCuts.b101 XCuts.z102 XCuts.b102 XCuts.n101 XCuts.v101 eq_refl XJ0101.seg).
Definition k102 := XR_trans _ _ _ _ _ _ _ _ _ _ k101 (XTop.xrun_seg_sound XCuts.z102 XCuts.b102 XCuts.z103 XCuts.b103 XCuts.n102 XCuts.v102 eq_refl XJ0102.seg).
Definition k103 := XR_trans _ _ _ _ _ _ _ _ _ _ k102 (XTop.xrun_seg_sound XCuts.z103 XCuts.b103 XCuts.z104 XCuts.b104 XCuts.n103 XCuts.v103 eq_refl XJ0103.seg).
Definition k104 := XR_trans _ _ _ _ _ _ _ _ _ _ k103 (XTop.xrun_seg_sound XCuts.z104 XCuts.b104 XCuts.z105 XCuts.b105 XCuts.n104 XCuts.v104 eq_refl XJ0104.seg).
Definition k105 := XR_trans _ _ _ _ _ _ _ _ _ _ k104 (XTop.xrun_seg_sound XCuts.z105 XCuts.b105 XCuts.z106 XCuts.b106 XCuts.n105 XCuts.v105 eq_refl XJ0105.seg).
Definition k106 := XR_trans _ _ _ _ _ _ _ _ _ _ k105 (XTop.xrun_seg_sound XCuts.z106 XCuts.b106 XCuts.z107 XCuts.b107 XCuts.n106 XCuts.v106 eq_refl XJ0106.seg).
Definition k107 := XR_trans _ _ _ _ _ _ _ _ _ _ k106 (XTop.xrun_seg_sound XCuts.z107 XCuts.b107 XCuts.z108 XCuts.b108 XCuts.n107 XCuts.v107 eq_refl XJ0107.seg).
Definition k108 := XR_trans _ _ _ _ _ _ _ _ _ _ k107 (XTop.xrun_seg_sound XCuts.z108 XCuts.b108 XCuts.z109 XCuts.b109 XCuts.n108 XCuts.v108 eq_refl XJ0108.seg).
Definition k109 := XR_trans _ _ _ _ _ _ _ _ _ _ k108 (XTop.xrun_seg_sound XCuts.z109 XCuts.b109 XCuts.z110 XCuts.b110 XCuts.n109 XCuts.v109 eq_refl XJ0109.seg).
Definition k110 := XR_trans _ _ _ _ _ _ _ _ _ _ k109 (XTop.xrun_seg_sound XCuts.z110 XCuts.b110 XCuts.z111 XCuts.b111 XCuts.n110 XCuts.v110 eq_refl XJ0110.seg).
Definition k111 := XR_trans _ _ _ _ _ _ _ _ _ _ k110 (XTop.xrun_seg_sound XCuts.z111 XCuts.b111 XCuts.z112 XCuts.b112 XCuts.n111 XCuts.v111 eq_refl XJ0111.seg).
Definition k112 := XR_trans _ _ _ _ _ _ _ _ _ _ k111 (XTop.xrun_seg_sound XCuts.z112 XCuts.b112 XCuts.z113 XCuts.b113 XCuts.n112 XCuts.v112 eq_refl XJ0112.seg).
Definition k113 := XR_trans _ _ _ _ _ _ _ _ _ _ k112 (XTop.xrun_seg_sound XCuts.z113 XCuts.b113 XCuts.z114 XCuts.b114 XCuts.n113 XCuts.v113 eq_refl XJ0113.seg).
Definition k114 := XR_trans _ _ _ _ _ _ _ _ _ _ k113 (XTop.xrun_seg_sound XCuts.z114 XCuts.b114 XCuts.z115 XCuts.b115 XCuts.n114 XCuts.v114 eq_refl XJ0114.seg).
Definition k115 := XR_trans _ _ _ _ _ _ _ _ _ _ k114 (XTop.xrun_seg_sound XCuts.z115 XCuts.b115 XCuts.z116 XCuts.b116 XCuts.n115 XCuts.v115 eq_refl XJ0115.seg).
Definition k116 := XR_trans _ _ _ _ _ _ _ _ _ _ k115 (XTop.xrun_seg_sound XCuts.z116 XCuts.b116 XCuts.z117 XCuts.b117 XCuts.n116 XCuts.v116 eq_refl XJ0116.seg).
Definition k117 := XR_trans _ _ _ _ _ _ _ _ _ _ k116 (XTop.xrun_seg_sound XCuts.z117 XCuts.b117 XCuts.z118 XCuts.b118 XCuts.n117 XCuts.v117 eq_refl XJ0117.seg).
Definition k118 := XR_trans _ _ _ _ _ _ _ _ _ _ k117 (XTop.xrun_seg_sound XCuts.z118 XCuts.b118 XCuts.z119 XCuts.b119 XCuts.n118 XCuts.v118 eq_refl XJ0118.seg).
Definition k119 := XR_trans _ _ _ _ _ _ _ _ _ _ k118 (XTop.xrun_seg_sound XCuts.z119 XCuts.b119 XCuts.z120 XCuts.b120 XCuts.n119 XCuts.v119 eq_refl XJ0119.seg).
Definition k120 := XR_trans _ _ _ _ _ _ _ _ _ _ k119 (XTop.xrun_seg_sound XCuts.z120 XCuts.b120 XCuts.z121 XCuts.b121 XCuts.n120 XCuts.v120 eq_refl XJ0120.seg).
Definition k121 := XR_trans _ _ _ _ _ _ _ _ _ _ k120 (XTop.xrun_seg_sound XCuts.z121 XCuts.b121 XCuts.z122 XCuts.b122 XCuts.n121 XCuts.v121 eq_refl XJ0121.seg).
Definition k122 := XR_trans _ _ _ _ _ _ _ _ _ _ k121 (XTop.xrun_seg_sound XCuts.z122 XCuts.b122 XCuts.z123 XCuts.b123 XCuts.n122 XCuts.v122 eq_refl XJ0122.seg).
Definition k123 := XR_trans _ _ _ _ _ _ _ _ _ _ k122 (XTop.xrun_seg_sound XCuts.z123 XCuts.b123 XCuts.z124 XCuts.b124 XCuts.n123 XCuts.v123 eq_refl XJ0123.seg).
Definition k124 := XR_trans _ _ _ _ _ _ _ _ _ _ k123 (XTop.xrun_seg_sound XCuts.z124 XCuts.b124 XCuts.z125 XCuts.b125 XCuts.n124 XCuts.v124 eq_refl XJ0124.seg).
Definition k125 := XR_trans _ _ _ _ _ _ _ _ _ _ k124 (XTop.xrun_seg_sound XCuts.z125 XCuts.b125 XCuts.z126 XCuts.b126 XCuts.n125 XCuts.v125 eq_refl XJ0125.seg).
Definition k126 := XR_trans _ _ _ _ _ _ _ _ _ _ k125 (XTop.xrun_seg_sound XCuts.z126 XCuts.b126 XCuts.z127 XCuts.b127 XCuts.n126 XCuts.v126 eq_refl XJ0126.seg).
Definition k127 := XR_trans _ _ _ _ _ _ _ _ _ _ k126 (XTop.xrun_seg_sound XCuts.z127 XCuts.b127 XCuts.z128 XCuts.b128 XCuts.n127 XCuts.v127 eq_refl XJ0127.seg).
Definition k128 := XR_trans _ _ _ _ _ _ _ _ _ _ k127 (XTop.xrun_seg_sound XCuts.z128 XCuts.b128 XCuts.z129 XCuts.b129 XCuts.n128 XCuts.v128 eq_refl XJ0128.seg).
Definition k129 := XR_trans _ _ _ _ _ _ _ _ _ _ k128 (XTop.xrun_seg_sound XCuts.z129 XCuts.b129 XCuts.z130 XCuts.b130 XCuts.n129 XCuts.v129 eq_refl XJ0129.seg).
Definition k130 := XR_trans _ _ _ _ _ _ _ _ _ _ k129 (XTop.xrun_seg_sound XCuts.z130 XCuts.b130 XCuts.z131 XCuts.b131 XCuts.n130 XCuts.v130 eq_refl XJ0130.seg).
Definition k131 := XR_trans _ _ _ _ _ _ _ _ _ _ k130 (XTop.xrun_seg_sound XCuts.z131 XCuts.b131 XCuts.z132 XCuts.b132 XCuts.n131 XCuts.v131 eq_refl XJ0131.seg).
Definition k132 := XR_trans _ _ _ _ _ _ _ _ _ _ k131 (XTop.xrun_seg_sound XCuts.z132 XCuts.b132 XCuts.z133 XCuts.b133 XCuts.n132 XCuts.v132 eq_refl XJ0132.seg).
Definition k133 := XR_trans _ _ _ _ _ _ _ _ _ _ k132 (XTop.xrun_seg_sound XCuts.z133 XCuts.b133 XCuts.z134 XCuts.b134 XCuts.n133 XCuts.v133 eq_refl XJ0133.seg).
Definition k134 := XR_trans _ _ _ _ _ _ _ _ _ _ k133 (XTop.xrun_seg_sound XCuts.z134 XCuts.b134 XCuts.z135 XCuts.b135 XCuts.n134 XCuts.v134 eq_refl XJ0134.seg).
Definition k135 := XR_trans _ _ _ _ _ _ _ _ _ _ k134 (XTop.xrun_seg_sound XCuts.z135 XCuts.b135 XCuts.z136 XCuts.b136 XCuts.n135 XCuts.v135 eq_refl XJ0135.seg).
Definition k136 := XR_trans _ _ _ _ _ _ _ _ _ _ k135 (XTop.xrun_seg_sound XCuts.z136 XCuts.b136 XCuts.z137 XCuts.b137 XCuts.n136 XCuts.v136 eq_refl XJ0136.seg).
Definition k137 := XR_trans _ _ _ _ _ _ _ _ _ _ k136 (XTop.xrun_seg_sound XCuts.z137 XCuts.b137 XCuts.z138 XCuts.b138 XCuts.n137 XCuts.v137 eq_refl XJ0137.seg).
Definition k138 := XR_trans _ _ _ _ _ _ _ _ _ _ k137 (XTop.xrun_seg_sound XCuts.z138 XCuts.b138 XCuts.z139 XCuts.b139 XCuts.n138 XCuts.v138 eq_refl XJ0138.seg).
Definition k139 := XR_trans _ _ _ _ _ _ _ _ _ _ k138 (XTop.xrun_seg_sound XCuts.z139 XCuts.b139 XCuts.z140 XCuts.b140 XCuts.n139 XCuts.v139 eq_refl XJ0139.seg).
Definition k140 := XR_trans _ _ _ _ _ _ _ _ _ _ k139 (XTop.xrun_seg_sound XCuts.z140 XCuts.b140 XCuts.z141 XCuts.b141 XCuts.n140 XCuts.v140 eq_refl XJ0140.seg).
Definition k141 := XR_trans _ _ _ _ _ _ _ _ _ _ k140 (XTop.xrun_seg_sound XCuts.z141 XCuts.b141 XCuts.z142 XCuts.b142 XCuts.n141 XCuts.v141 eq_refl XJ0141.seg).
Definition k142 := XR_trans _ _ _ _ _ _ _ _ _ _ k141 (XTop.xrun_seg_sound XCuts.z142 XCuts.b142 XCuts.z143 XCuts.b143 XCuts.n142 XCuts.v142 eq_refl XJ0142.seg).
Definition k143 := XR_trans _ _ _ _ _ _ _ _ _ _ k142 (XTop.xrun_seg_sound XCuts.z143 XCuts.b143 XCuts.z144 XCuts.b144 XCuts.n143 XCuts.v143 eq_refl XJ0143.seg).
Definition k144 := XR_trans _ _ _ _ _ _ _ _ _ _ k143 (XTop.xrun_seg_sound XCuts.z144 XCuts.b144 XCuts.z145 XCuts.b145 XCuts.n144 XCuts.v144 eq_refl XJ0144.seg).
Definition k145 := XR_trans _ _ _ _ _ _ _ _ _ _ k144 (XTop.xrun_seg_sound XCuts.z145 XCuts.b145 XCuts.z146 XCuts.b146 XCuts.n145 XCuts.v145 eq_refl XJ0145.seg).
Definition k146 := XR_trans _ _ _ _ _ _ _ _ _ _ k145 (XTop.xrun_seg_sound XCuts.z146 XCuts.b146 XCuts.z147 XCuts.b147 XCuts.n146 XCuts.v146 eq_refl XJ0146.seg).
Definition k147 := XR_trans _ _ _ _ _ _ _ _ _ _ k146 (XTop.xrun_seg_sound XCuts.z147 XCuts.b147 XCuts.z148 XCuts.b148 XCuts.n147 XCuts.v147 eq_refl XJ0147.seg).
Definition k148 := XR_trans _ _ _ _ _ _ _ _ _ _ k147 (XTop.xrun_seg_sound XCuts.z148 XCuts.b148 XCuts.z149 XCuts.b149 XCuts.n148 XCuts.v148 eq_refl XJ0148.seg).
Definition k149 := XR_trans _ _ _ _ _ _ _ _ _ _ k148 (XTop.xrun_seg_sound XCuts.z149 XCuts.b149 XCuts.z150 XCuts.b150 XCuts.n149 XCuts.v149 eq_refl XJ0149.seg).
Definition k150 := XR_trans _ _ _ _ _ _ _ _ _ _ k149 (XTop.xrun_seg_sound XCuts.z150 XCuts.b150 XCuts.z151 XCuts.b151 XCuts.n150 XCuts.v150 eq_refl XJ0150.seg).
Definition k151 := XR_trans _ _ _ _ _ _ _ _ _ _ k150 (XTop.xrun_seg_sound XCuts.z151 XCuts.b151 XCuts.z152 XCuts.b152 XCuts.n151 XCuts.v151 eq_refl XJ0151.seg).
Definition k152 := XR_trans _ _ _ _ _ _ _ _ _ _ k151 (XTop.xrun_seg_sound XCuts.z152 XCuts.b152 XCuts.z153 XCuts.b153 XCuts.n152 XCuts.v152 eq_refl XJ0152.seg).
Definition k153 := XR_trans _ _ _ _ _ _ _ _ _ _ k152 (XTop.xrun_seg_sound XCuts.z153 XCuts.b153 XCuts.z154 XCuts.b154 XCuts.n153 XCuts.v153 eq_refl XJ0153.seg).
Definition k154 := XR_trans _ _ _ _ _ _ _ _ _ _ k153 (XTop.xrun_seg_sound XCuts.z154 XCuts.b154 XCuts.z155 XCuts.b155 XCuts.n154 XCuts.v154 eq_refl XJ0154.seg).
Definition k155 := XR_trans _ _ _ _ _ _ _ _ _ _ k154 (XTop.xrun_seg_sound XCuts.z155 XCuts.b155 XCuts.z156 XCuts.b156 XCuts.n155 XCuts.v155 eq_refl XJ0155.seg).
Definition k156 := XR_trans _ _ _ _ _ _ _ _ _ _ k155 (XTop.xrun_seg_sound XCuts.z156 XCuts.b156 XCuts.z157 XCuts.b157 XCuts.n156 XCuts.v156 eq_refl XJ0156.seg).
Definition k157 := XR_trans _ _ _ _ _ _ _ _ _ _ k156 (XTop.xrun_seg_sound XCuts.z157 XCuts.b157 XCuts.z158 XCuts.b158 XCuts.n157 XCuts.v157 eq_refl XJ0157.seg).
Definition k158 := XR_trans _ _ _ _ _ _ _ _ _ _ k157 (XTop.xrun_seg_sound XCuts.z158 XCuts.b158 XCuts.z159 XCuts.b159 XCuts.n158 XCuts.v158 eq_refl XJ0158.seg).
Definition k159 := XR_trans _ _ _ _ _ _ _ _ _ _ k158 (XTop.xrun_seg_sound XCuts.z159 XCuts.b159 XCuts.z160 XCuts.b160 XCuts.n159 XCuts.v159 eq_refl XJ0159.seg).
Definition k160 := XR_trans _ _ _ _ _ _ _ _ _ _ k159 (XTop.xrun_seg_sound XCuts.z160 XCuts.b160 XCuts.z161 XCuts.b161 XCuts.n160 XCuts.v160 eq_refl XJ0160.seg).
Definition k161 := XR_trans _ _ _ _ _ _ _ _ _ _ k160 (XTop.xrun_seg_sound XCuts.z161 XCuts.b161 XCuts.z162 XCuts.b162 XCuts.n161 XCuts.v161 eq_refl XJ0161.seg).
Definition k162 := XR_trans _ _ _ _ _ _ _ _ _ _ k161 (XTop.xrun_seg_sound XCuts.z162 XCuts.b162 XCuts.z163 XCuts.b163 XCuts.n162 XCuts.v162 eq_refl XJ0162.seg).
Definition k163 := XR_trans _ _ _ _ _ _ _ _ _ _ k162 (XTop.xrun_seg_sound XCuts.z163 XCuts.b163 XCuts.z164 XCuts.b164 XCuts.n163 XCuts.v163 eq_refl XJ0163.seg).
Definition k164 := XR_trans _ _ _ _ _ _ _ _ _ _ k163 (XTop.xrun_seg_sound XCuts.z164 XCuts.b164 XCuts.z165 XCuts.b165 XCuts.n164 XCuts.v164 eq_refl XJ0164.seg).
Definition k165 := XR_trans _ _ _ _ _ _ _ _ _ _ k164 (XTop.xrun_seg_sound XCuts.z165 XCuts.b165 XCuts.z166 XCuts.b166 XCuts.n165 XCuts.v165 eq_refl XJ0165.seg).
Definition k166 := XR_trans _ _ _ _ _ _ _ _ _ _ k165 (XTop.xrun_seg_sound XCuts.z166 XCuts.b166 XCuts.z167 XCuts.b167 XCuts.n166 XCuts.v166 eq_refl XJ0166.seg).
Definition k167 := XR_trans _ _ _ _ _ _ _ _ _ _ k166 (XTop.xrun_seg_sound XCuts.z167 XCuts.b167 XCuts.z168 XCuts.b168 XCuts.n167 XCuts.v167 eq_refl XJ0167.seg).
Definition k168 := XR_trans _ _ _ _ _ _ _ _ _ _ k167 (XTop.xrun_seg_sound XCuts.z168 XCuts.b168 XCuts.z169 XCuts.b169 XCuts.n168 XCuts.v168 eq_refl XJ0168.seg).
Definition k169 := XR_trans _ _ _ _ _ _ _ _ _ _ k168 (XTop.xrun_seg_sound XCuts.z169 XCuts.b169 XCuts.z170 XCuts.b170 XCuts.n169 XCuts.v169 eq_refl XJ0169.seg).
Definition k170 := XR_trans _ _ _ _ _ _ _ _ _ _ k169 (XTop.xrun_seg_sound XCuts.z170 XCuts.b170 XCuts.z171 XCuts.b171 XCuts.n170 XCuts.v170 eq_refl XJ0170.seg).
Definition k171 := XR_trans _ _ _ _ _ _ _ _ _ _ k170 (XTop.xrun_seg_sound XCuts.z171 XCuts.b171 XCuts.z172 XCuts.b172 XCuts.n171 XCuts.v171 eq_refl XJ0171.seg).
Definition k172 := XR_trans _ _ _ _ _ _ _ _ _ _ k171 (XTop.xrun_seg_sound XCuts.z172 XCuts.b172 XCuts.z173 XCuts.b173 XCuts.n172 XCuts.v172 eq_refl XJ0172.seg).
Definition k173 := XR_trans _ _ _ _ _ _ _ _ _ _ k172 (XTop.xrun_seg_sound XCuts.z173 XCuts.b173 XCuts.z174 XCuts.b174 XCuts.n173 XCuts.v173 eq_refl XJ0173.seg).
Definition k174 := XR_trans _ _ _ _ _ _ _ _ _ _ k173 (XTop.xrun_seg_sound XCuts.z174 XCuts.b174 XCuts.z175 XCuts.b175 XCuts.n174 XCuts.v174 eq_refl XJ0174.seg).
Definition k175 := XR_trans _ _ _ _ _ _ _ _ _ _ k174 (XTop.xrun_seg_sound XCuts.z175 XCuts.b175 XCuts.z176 XCuts.b176 XCuts.n175 XCuts.v175 eq_refl XJ0175.seg).
Definition k176 := XR_trans _ _ _ _ _ _ _ _ _ _ k175 (XTop.xrun_seg_sound XCuts.z176 XCuts.b176 XCuts.z177 XCuts.b177 XCuts.n176 XCuts.v176 eq_refl XJ0176.seg).
Definition k177 := XR_trans _ _ _ _ _ _ _ _ _ _ k176 (XTop.xrun_seg_sound XCuts.z177 XCuts.b177 XCuts.z178 XCuts.b178 XCuts.n177 XCuts.v177 eq_refl XJ0177.seg).
Definition k178 := XR_trans _ _ _ _ _ _ _ _ _ _ k177 (XTop.xrun_seg_sound XCuts.z178 XCuts.b178 XCuts.z179 XCuts.b179 XCuts.n178 XCuts.v178 eq_refl XJ0178.seg).
Definition k179 := XR_trans _ _ _ _ _ _ _ _ _ _ k178 (XTop.xrun_seg_sound XCuts.z179 XCuts.b179 XCuts.z180 XCuts.b180 XCuts.n179 XCuts.v179 eq_refl XJ0179.seg).
Definition k180 := XR_trans _ _ _ _ _ _ _ _ _ _ k179 (XTop.xrun_seg_sound XCuts.z180 XCuts.b180 XCuts.z181 XCuts.b181 XCuts.n180 XCuts.v180 eq_refl XJ0180.seg).
Definition k181 := XR_trans _ _ _ _ _ _ _ _ _ _ k180 (XTop.xrun_seg_sound XCuts.z181 XCuts.b181 XCuts.z182 XCuts.b182 XCuts.n181 XCuts.v181 eq_refl XJ0181.seg).
Definition k182 := XR_trans _ _ _ _ _ _ _ _ _ _ k181 (XTop.xrun_seg_sound XCuts.z182 XCuts.b182 XCuts.z183 XCuts.b183 XCuts.n182 XCuts.v182 eq_refl XJ0182.seg).
Definition k183 := XR_trans _ _ _ _ _ _ _ _ _ _ k182 (XTop.xrun_seg_sound XCuts.z183 XCuts.b183 XCuts.z184 XCuts.b184 XCuts.n183 XCuts.v183 eq_refl XJ0183.seg).
Definition k184 := XR_trans _ _ _ _ _ _ _ _ _ _ k183 (XTop.xrun_seg_sound XCuts.z184 XCuts.b184 XCuts.z185 XCuts.b185 XCuts.n184 XCuts.v184 eq_refl XJ0184.seg).
Definition k185 := XR_trans _ _ _ _ _ _ _ _ _ _ k184 (XTop.xrun_seg_sound XCuts.z185 XCuts.b185 XCuts.z186 XCuts.b186 XCuts.n185 XCuts.v185 eq_refl XJ0185.seg).
Definition k186 := XR_trans _ _ _ _ _ _ _ _ _ _ k185 (XTop.xrun_seg_sound XCuts.z186 XCuts.b186 XCuts.z187 XCuts.b187 XCuts.n186 XCuts.v186 eq_refl XJ0186.seg).
Definition k187 := XR_trans _ _ _ _ _ _ _ _ _ _ k186 (XTop.xrun_seg_sound XCuts.z187 XCuts.b187 XCuts.z188 XCuts.b188 XCuts.n187 XCuts.v187 eq_refl XJ0187.seg).
Definition k188 := XR_trans _ _ _ _ _ _ _ _ _ _ k187 (XTop.xrun_seg_sound XCuts.z188 XCuts.b188 XCuts.z189 XCuts.b189 XCuts.n188 XCuts.v188 eq_refl XJ0188.seg).
Definition k189 := XR_trans _ _ _ _ _ _ _ _ _ _ k188 (XTop.xrun_seg_sound XCuts.z189 XCuts.b189 XCuts.z190 XCuts.b190 XCuts.n189 XCuts.v189 eq_refl XJ0189.seg).
Definition k190 := XR_trans _ _ _ _ _ _ _ _ _ _ k189 (XTop.xrun_seg_sound XCuts.z190 XCuts.b190 XCuts.z191 XCuts.b191 XCuts.n190 XCuts.v190 eq_refl XJ0190.seg).
Definition k191 := XR_trans _ _ _ _ _ _ _ _ _ _ k190 (XTop.xrun_seg_sound XCuts.z191 XCuts.b191 XCuts.z192 XCuts.b192 XCuts.n191 XCuts.v191 eq_refl XJ0191.seg).
Definition k192 := XR_trans _ _ _ _ _ _ _ _ _ _ k191 (XTop.xrun_seg_sound XCuts.z192 XCuts.b192 XCuts.z193 XCuts.b193 XCuts.n192 XCuts.v192 eq_refl XJ0192.seg).
Definition k193 := XR_trans _ _ _ _ _ _ _ _ _ _ k192 (XTop.xrun_seg_sound XCuts.z193 XCuts.b193 XCuts.z194 XCuts.b194 XCuts.n193 XCuts.v193 eq_refl XJ0193.seg).
Definition k194 := XR_trans _ _ _ _ _ _ _ _ _ _ k193 (XTop.xrun_seg_sound XCuts.z194 XCuts.b194 XCuts.z195 XCuts.b195 XCuts.n194 XCuts.v194 eq_refl XJ0194.seg).
Definition k195 := XR_trans _ _ _ _ _ _ _ _ _ _ k194 (XTop.xrun_seg_sound XCuts.z195 XCuts.b195 XCuts.z196 XCuts.b196 XCuts.n195 XCuts.v195 eq_refl XJ0195.seg).
Definition k196 := XR_trans _ _ _ _ _ _ _ _ _ _ k195 (XTop.xrun_seg_sound XCuts.z196 XCuts.b196 XCuts.z197 XCuts.b197 XCuts.n196 XCuts.v196 eq_refl XJ0196.seg).
Definition k197 := XR_trans _ _ _ _ _ _ _ _ _ _ k196 (XTop.xrun_seg_sound XCuts.z197 XCuts.b197 XCuts.z198 XCuts.b198 XCuts.n197 XCuts.v197 eq_refl XJ0197.seg).
Definition k198 := XR_trans _ _ _ _ _ _ _ _ _ _ k197 (XTop.xrun_seg_sound XCuts.z198 XCuts.b198 XCuts.z199 XCuts.b199 XCuts.n198 XCuts.v198 eq_refl XJ0198.seg).
Definition k199 := XR_trans _ _ _ _ _ _ _ _ _ _ k198 (XTop.xrun_seg_sound XCuts.z199 XCuts.b199 XCuts.z200 XCuts.b200 XCuts.n199 XCuts.v199 eq_refl XJ0199.seg).
Definition k200 := XR_trans _ _ _ _ _ _ _ _ _ _ k199 (XTop.xrun_seg_sound XCuts.z200 XCuts.b200 XCuts.z201 XCuts.b201 XCuts.n200 XCuts.v200 eq_refl XJ0200.seg).
Definition k201 := XR_trans _ _ _ _ _ _ _ _ _ _ k200 (XTop.xrun_seg_sound XCuts.z201 XCuts.b201 XCuts.z202 XCuts.b202 XCuts.n201 XCuts.v201 eq_refl XJ0201.seg).
Definition k202 := XR_trans _ _ _ _ _ _ _ _ _ _ k201 (XTop.xrun_seg_sound XCuts.z202 XCuts.b202 XCuts.z203 XCuts.b203 XCuts.n202 XCuts.v202 eq_refl XJ0202.seg).
Definition k203 := XR_trans _ _ _ _ _ _ _ _ _ _ k202 (XTop.xrun_seg_sound XCuts.z203 XCuts.b203 XCuts.z204 XCuts.b204 XCuts.n203 XCuts.v203 eq_refl XJ0203.seg).
Definition k204 := XR_trans _ _ _ _ _ _ _ _ _ _ k203 (XTop.xrun_seg_sound XCuts.z204 XCuts.b204 XCuts.z205 XCuts.b205 XCuts.n204 XCuts.v204 eq_refl XJ0204.seg).
Definition k205 := XR_trans _ _ _ _ _ _ _ _ _ _ k204 (XTop.xrun_seg_sound XCuts.z205 XCuts.b205 XCuts.z206 XCuts.b206 XCuts.n205 XCuts.v205 eq_refl XJ0205.seg).
Definition k206 := XR_trans _ _ _ _ _ _ _ _ _ _ k205 (XTop.xrun_seg_sound XCuts.z206 XCuts.b206 XCuts.z207 XCuts.b207 XCuts.n206 XCuts.v206 eq_refl XJ0206.seg).
Definition k207 := XR_trans _ _ _ _ _ _ _ _ _ _ k206 (XTop.xrun_seg_sound XCuts.z207 XCuts.b207 XCuts.z208 XCuts.b208 XCuts.n207 XCuts.v207 eq_refl XJ0207.seg).
Definition k208 := XR_trans _ _ _ _ _ _ _ _ _ _ k207 (XTop.xrun_seg_sound XCuts.z208 XCuts.b208 XCuts.z209 XCuts.b209 XCuts.n208 XCuts.v208 eq_refl XJ0208.seg).
Definition k209 := XR_trans _ _ _ _ _ _ _ _ _ _ k208 (XTop.xrun_seg_sound XCuts.z209 XCuts.b209 XCuts.z210 XCuts.b210 XCuts.n209 XCuts.v209 eq_refl XJ0209.seg).
Definition k210 := XR_trans _ _ _ _ _ _ _ _ _ _ k209 (XTop.xrun_seg_sound XCuts.z210 XCuts.b210 XCuts.z211 XCuts.b211 XCuts.n210 XCuts.v210 eq_refl XJ0210.seg).
Definition k211 := XR_trans _ _ _ _ _ _ _ _ _ _ k210 (XTop.xrun_seg_sound XCuts.z211 XCuts.b211 XCuts.z212 XCuts.b212 XCuts.n211 XCuts.v211 eq_refl XJ0211.seg).
Definition k212 := XR_trans _ _ _ _ _ _ _ _ _ _ k211 (XTop.xrun_seg_sound XCuts.z212 XCuts.b212 XCuts.z213 XCuts.b213 XCuts.n212 XCuts.v212 eq_refl XJ0212.seg).
Definition k213 := XR_trans _ _ _ _ _ _ _ _ _ _ k212 (XTop.xrun_seg_sound XCuts.z213 XCuts.b213 XCuts.z214 XCuts.b214 XCuts.n213 XCuts.v213 eq_refl XJ0213.seg).
Definition k214 := XR_trans _ _ _ _ _ _ _ _ _ _ k213 (XTop.xrun_seg_sound XCuts.z214 XCuts.b214 XCuts.z215 XCuts.b215 XCuts.n214 XCuts.v214 eq_refl XJ0214.seg).
Definition k215 := XR_trans _ _ _ _ _ _ _ _ _ _ k214 (XTop.xrun_seg_sound XCuts.z215 XCuts.b215 XCuts.z216 XCuts.b216 XCuts.n215 XCuts.v215 eq_refl XJ0215.seg).
Definition k216 := XR_trans _ _ _ _ _ _ _ _ _ _ k215 (XTop.xrun_seg_sound XCuts.z216 XCuts.b216 XCuts.z217 XCuts.b217 XCuts.n216 XCuts.v216 eq_refl XJ0216.seg).
Definition k217 := XR_trans _ _ _ _ _ _ _ _ _ _ k216 (XTop.xrun_seg_sound XCuts.z217 XCuts.b217 XCuts.z218 XCuts.b218 XCuts.n217 XCuts.v217 eq_refl XJ0217.seg).
Definition k218 := XR_trans _ _ _ _ _ _ _ _ _ _ k217 (XTop.xrun_seg_sound XCuts.z218 XCuts.b218 XCuts.z219 XCuts.b219 XCuts.n218 XCuts.v218 eq_refl XJ0218.seg).
Definition k219 := XR_trans _ _ _ _ _ _ _ _ _ _ k218 (XTop.xrun_seg_sound XCuts.z219 XCuts.b219 XCuts.z220 XCuts.b220 XCuts.n219 XCuts.v219 eq_refl XJ0219.seg).
Definition k220 := XR_trans _ _ _ _ _ _ _ _ _ _ k219 (XTop.xrun_seg_sound XCuts.z220 XCuts.b220 XCuts.z221 XCuts.b221 XCuts.n220 XCuts.v220 eq_refl XJ0220.seg).
Definition k221 := XR_trans _ _ _ _ _ _ _ _ _ _ k220 (XTop.xrun_seg_sound XCuts.z221 XCuts.b221 XCuts.z222 XCuts.b222 XCuts.n221 XCuts.v221 eq_refl XJ0221.seg).
Definition k222 := XR_trans _ _ _ _ _ _ _ _ _ _ k221 (XTop.xrun_seg_sound XCuts.z222 XCuts.b222 XCuts.z223 XCuts.b223 XCuts.n222 XCuts.v222 eq_refl XJ0222.seg).
Definition k223 := XR_trans _ _ _ _ _ _ _ _ _ _ k222 (XTop.xrun_seg_sound XCuts.z223 XCuts.b223 XCuts.z224 XCuts.b224 XCuts.n223 XCuts.v223 eq_refl XJ0223.seg).
Definition k224 := XR_trans _ _ _ _ _ _ _ _ _ _ k223 (XTop.xrun_seg_sound XCuts.z224 XCuts.b224 XCuts.z225 XCuts.b225 XCuts.n224 XCuts.v224 eq_refl XJ0224.seg).
Definition k225 := XR_trans _ _ _ _ _ _ _ _ _ _ k224 (XTop.xrun_seg_sound XCuts.z225 XCuts.b225 XCuts.z226 XCuts.b226 XCuts.n225 XCuts.v225 eq_refl XJ0225.seg).
Definition k226 := XR_trans _ _ _ _ _ _ _ _ _ _ k225 (XTop.xrun_seg_sound XCuts.z226 XCuts.b226 XCuts.z227 XCuts.b227 XCuts.n226 XCuts.v226 eq_refl XJ0226.seg).
Definition k227 := XR_trans _ _ _ _ _ _ _ _ _ _ k226 (XTop.xrun_seg_sound XCuts.z227 XCuts.b227 XCuts.z228 XCuts.b228 XCuts.n227 XCuts.v227 eq_refl XJ0227.seg).
Definition k228 := XR_trans _ _ _ _ _ _ _ _ _ _ k227 (XTop.xrun_seg_sound XCuts.z228 XCuts.b228 XCuts.z229 XCuts.b229 XCuts.n228 XCuts.v228 eq_refl XJ0228.seg).
Definition k229 := XR_trans _ _ _ _ _ _ _ _ _ _ k228 (XTop.xrun_seg_sound XCuts.z229 XCuts.b229 XCuts.z230 XCuts.b230 XCuts.n229 XCuts.v229 eq_refl XJ0229.seg).
Definition k230 := XR_trans _ _ _ _ _ _ _ _ _ _ k229 (XTop.xrun_seg_sound XCuts.z230 XCuts.b230 XCuts.z231 XCuts.b231 XCuts.n230 XCuts.v230 eq_refl XJ0230.seg).
Definition k231 := XR_trans _ _ _ _ _ _ _ _ _ _ k230 (XTop.xrun_seg_sound XCuts.z231 XCuts.b231 XCuts.z232 XCuts.b232 XCuts.n231 XCuts.v231 eq_refl XJ0231.seg).
Definition k232 := XR_trans _ _ _ _ _ _ _ _ _ _ k231 (XTop.xrun_seg_sound XCuts.z232 XCuts.b232 XCuts.z233 XCuts.b233 XCuts.n232 XCuts.v232 eq_refl XJ0232.seg).
Definition k233 := XR_trans _ _ _ _ _ _ _ _ _ _ k232 (XTop.xrun_seg_sound XCuts.z233 XCuts.b233 XCuts.z234 XCuts.b234 XCuts.n233 XCuts.v233 eq_refl XJ0233.seg).
Definition k234 := XR_trans _ _ _ _ _ _ _ _ _ _ k233 (XTop.xrun_seg_sound XCuts.z234 XCuts.b234 XCuts.z235 XCuts.b235 XCuts.n234 XCuts.v234 eq_refl XJ0234.seg).
Definition k235 := XR_trans _ _ _ _ _ _ _ _ _ _ k234 (XTop.xrun_seg_sound XCuts.z235 XCuts.b235 XCuts.z236 XCuts.b236 XCuts.n235 XCuts.v235 eq_refl XJ0235.seg).
Definition k236 := XR_trans _ _ _ _ _ _ _ _ _ _ k235 (XTop.xrun_seg_sound XCuts.z236 XCuts.b236 XCuts.z237 XCuts.b237 XCuts.n236 XCuts.v236 eq_refl XJ0236.seg).
Definition k237 := XR_trans _ _ _ _ _ _ _ _ _ _ k236 (XTop.xrun_seg_sound XCuts.z237 XCuts.b237 XCuts.z238 XCuts.b238 XCuts.n237 XCuts.v237 eq_refl XJ0237.seg).
Definition k238 := XR_trans _ _ _ _ _ _ _ _ _ _ k237 (XTop.xrun_seg_sound XCuts.z238 XCuts.b238 XCuts.z239 XCuts.b239 XCuts.n238 XCuts.v238 eq_refl XJ0238.seg).
Definition k239 := XR_trans _ _ _ _ _ _ _ _ _ _ k238 (XTop.xrun_seg_sound XCuts.z239 XCuts.b239 XCuts.z240 XCuts.b240 XCuts.n239 XCuts.v239 eq_refl XJ0239.seg).
Definition k240 := XR_trans _ _ _ _ _ _ _ _ _ _ k239 (XTop.xrun_seg_sound XCuts.z240 XCuts.b240 XCuts.z241 XCuts.b241 XCuts.n240 XCuts.v240 eq_refl XJ0240.seg).
Definition k241 := XR_trans _ _ _ _ _ _ _ _ _ _ k240 (XTop.xrun_seg_sound XCuts.z241 XCuts.b241 XCuts.z242 XCuts.b242 XCuts.n241 XCuts.v241 eq_refl XJ0241.seg).
Definition k242 := XR_trans _ _ _ _ _ _ _ _ _ _ k241 (XTop.xrun_seg_sound XCuts.z242 XCuts.b242 XCuts.z243 XCuts.b243 XCuts.n242 XCuts.v242 eq_refl XJ0242.seg).
Definition k243 := XR_trans _ _ _ _ _ _ _ _ _ _ k242 (XTop.xrun_seg_sound XCuts.z243 XCuts.b243 XCuts.z244 XCuts.b244 XCuts.n243 XCuts.v243 eq_refl XJ0243.seg).
Definition k244 := XR_trans _ _ _ _ _ _ _ _ _ _ k243 (XTop.xrun_seg_sound XCuts.z244 XCuts.b244 XCuts.z245 XCuts.b245 XCuts.n244 XCuts.v244 eq_refl XJ0244.seg).
Definition k245 := XR_trans _ _ _ _ _ _ _ _ _ _ k244 (XTop.xrun_seg_sound XCuts.z245 XCuts.b245 XCuts.z246 XCuts.b246 XCuts.n245 XCuts.v245 eq_refl XJ0245.seg).
Definition k246 := XR_trans _ _ _ _ _ _ _ _ _ _ k245 (XTop.xrun_seg_sound XCuts.z246 XCuts.b246 XCuts.z247 XCuts.b247 XCuts.n246 XCuts.v246 eq_refl XJ0246.seg).
Definition k247 := XR_trans _ _ _ _ _ _ _ _ _ _ k246 (XTop.xrun_seg_sound XCuts.z247 XCuts.b247 XCuts.z248 XCuts.b248 XCuts.n247 XCuts.v247 eq_refl XJ0247.seg).
Definition k248 := XR_trans _ _ _ _ _ _ _ _ _ _ k247 (XTop.xrun_seg_sound XCuts.z248 XCuts.b248 XCuts.z249 XCuts.b249 XCuts.n248 XCuts.v248 eq_refl XJ0248.seg).
Definition k249 := XR_trans _ _ _ _ _ _ _ _ _ _ k248 (XTop.xrun_seg_sound XCuts.z249 XCuts.b249 XCuts.z250 XCuts.b250 XCuts.n249 XCuts.v249 eq_refl XJ0249.seg).
Definition k250 := XR_trans _ _ _ _ _ _ _ _ _ _ k249 (XTop.xrun_seg_sound XCuts.z250 XCuts.b250 XCuts.z251 XCuts.b251 XCuts.n250 XCuts.v250 eq_refl XJ0250.seg).
Definition k251 := XR_trans _ _ _ _ _ _ _ _ _ _ k250 (XTop.xrun_seg_sound XCuts.z251 XCuts.b251 XCuts.z252 XCuts.b252 XCuts.n251 XCuts.v251 eq_refl XJ0251.seg).
Definition k252 := XR_trans _ _ _ _ _ _ _ _ _ _ k251 (XTop.xrun_seg_sound XCuts.z252 XCuts.b252 XCuts.z253 XCuts.b253 XCuts.n252 XCuts.v252 eq_refl XJ0252.seg).
Definition k253 := XR_trans _ _ _ _ _ _ _ _ _ _ k252 (XTop.xrun_seg_sound XCuts.z253 XCuts.b253 XCuts.z254 XCuts.b254 XCuts.n253 XCuts.v253 eq_refl XJ0253.seg).
Definition k254 := XR_trans _ _ _ _ _ _ _ _ _ _ k253 (XTop.xrun_seg_sound XCuts.z254 XCuts.b254 XCuts.z255 XCuts.b255 XCuts.n254 XCuts.v254 eq_refl XJ0254.seg).
Definition k255 := XR_trans _ _ _ _ _ _ _ _ _ _ k254 (XTop.xrun_seg_sound XCuts.z255 XCuts.b255 XCuts.z256 XCuts.b256 XCuts.n255 XCuts.v255 eq_refl XJ0255.seg).
Definition k256 := XR_trans _ _ _ _ _ _ _ _ _ _ k255 (XTop.xrun_seg_sound XCuts.z256 XCuts.b256 XCuts.z257 XCuts.b257 XCuts.n256 XCuts.v256 eq_refl XJ0256.seg).
Definition k257 := XR_trans _ _ _ _ _ _ _ _ _ _ k256 (XTop.xrun_seg_sound XCuts.z257 XCuts.b257 XCuts.z258 XCuts.b258 XCuts.n257 XCuts.v257 eq_refl XJ0257.seg).
Definition k258 := XR_trans _ _ _ _ _ _ _ _ _ _ k257 (XTop.xrun_seg_sound XCuts.z258 XCuts.b258 XCuts.z259 XCuts.b259 XCuts.n258 XCuts.v258 eq_refl XJ0258.seg).
Definition k259 := XR_trans _ _ _ _ _ _ _ _ _ _ k258 (XTop.xrun_seg_sound XCuts.z259 XCuts.b259 XCuts.z260 XCuts.b260 XCuts.n259 XCuts.v259 eq_refl XJ0259.seg).
Definition k260 := XR_trans _ _ _ _ _ _ _ _ _ _ k259 (XTop.xrun_seg_sound XCuts.z260 XCuts.b260 XCuts.z261 XCuts.b261 XCuts.n260 XCuts.v260 eq_refl XJ0260.seg).
Definition k261 := XR_trans _ _ _ _ _ _ _ _ _ _ k260 (XTop.xrun_seg_sound XCuts.z261 XCuts.b261 XCuts.z262 XCuts.b262 XCuts.n261 XCuts.v261 eq_refl XJ0261.seg).
Definition k262 := XR_trans _ _ _ _ _ _ _ _ _ _ k261 (XTop.xrun_seg_sound XCuts.z262 XCuts.b262 XCuts.z263 XCuts.b263 XCuts.n262 XCuts.v262 eq_refl XJ0262.seg).
Definition k263 := XR_trans _ _ _ _ _ _ _ _ _ _ k262 (XTop.xrun_seg_sound XCuts.z263 XCuts.b263 XCuts.z264 XCuts.b264 XCuts.n263 XCuts.v263 eq_refl XJ0263.seg).
Definition k264 := XR_trans _ _ _ _ _ _ _ _ _ _ k263 (XTop.xrun_seg_sound XCuts.z264 XCuts.b264 XCuts.z265 XCuts.b265 XCuts.n264 XCuts.v264 eq_refl XJ0264.seg).
Definition k265 := XR_trans _ _ _ _ _ _ _ _ _ _ k264 (XTop.xrun_seg_sound XCuts.z265 XCuts.b265 XCuts.z266 XCuts.b266 XCuts.n265 XCuts.v265 eq_refl XJ0265.seg).
Definition k266 := XR_trans _ _ _ _ _ _ _ _ _ _ k265 (XTop.xrun_seg_sound XCuts.z266 XCuts.b266 XCuts.z267 XCuts.b267 XCuts.n266 XCuts.v266 eq_refl XJ0266.seg).
Definition k267 := XR_trans _ _ _ _ _ _ _ _ _ _ k266 (XTop.xrun_seg_sound XCuts.z267 XCuts.b267 XCuts.z268 XCuts.b268 XCuts.n267 XCuts.v267 eq_refl XJ0267.seg).
Definition k268 := XR_trans _ _ _ _ _ _ _ _ _ _ k267 (XTop.xrun_seg_sound XCuts.z268 XCuts.b268 XCuts.z269 XCuts.b269 XCuts.n268 XCuts.v268 eq_refl XJ0268.seg).
Definition k269 := XR_trans _ _ _ _ _ _ _ _ _ _ k268 (XTop.xrun_seg_sound XCuts.z269 XCuts.b269 XCuts.z270 XCuts.b270 XCuts.n269 XCuts.v269 eq_refl XJ0269.seg).
Definition k270 := XR_trans _ _ _ _ _ _ _ _ _ _ k269 (XTop.xrun_seg_sound XCuts.z270 XCuts.b270 XCuts.z271 XCuts.b271 XCuts.n270 XCuts.v270 eq_refl XJ0270.seg).
Definition k271 := XR_trans _ _ _ _ _ _ _ _ _ _ k270 (XTop.xrun_seg_sound XCuts.z271 XCuts.b271 XCuts.z272 XCuts.b272 XCuts.n271 XCuts.v271 eq_refl XJ0271.seg).
Definition k272 := XR_trans _ _ _ _ _ _ _ _ _ _ k271 (XTop.xrun_seg_sound XCuts.z272 XCuts.b272 XCuts.z273 XCuts.b273 XCuts.n272 XCuts.v272 eq_refl XJ0272.seg).
Definition k273 := XR_trans _ _ _ _ _ _ _ _ _ _ k272 (XTop.xrun_seg_sound XCuts.z273 XCuts.b273 XCuts.z274 XCuts.b274 XCuts.n273 XCuts.v273 eq_refl XJ0273.seg).
Definition k274 := XR_trans _ _ _ _ _ _ _ _ _ _ k273 (XTop.xrun_seg_sound XCuts.z274 XCuts.b274 XCuts.z275 XCuts.b275 XCuts.n274 XCuts.v274 eq_refl XJ0274.seg).
Definition k275 := XR_trans _ _ _ _ _ _ _ _ _ _ k274 (XTop.xrun_seg_sound XCuts.z275 XCuts.b275 XCuts.z276 XCuts.b276 XCuts.n275 XCuts.v275 eq_refl XJ0275.seg).
Definition k276 := XR_trans _ _ _ _ _ _ _ _ _ _ k275 (XTop.xrun_seg_sound XCuts.z276 XCuts.b276 XCuts.z277 XCuts.b277 XCuts.n276 XCuts.v276 eq_refl XJ0276.seg).
Definition k277 := XR_trans _ _ _ _ _ _ _ _ _ _ k276 (XTop.xrun_seg_sound XCuts.z277 XCuts.b277 XCuts.z278 XCuts.b278 XCuts.n277 XCuts.v277 eq_refl XJ0277.seg).
Definition k278 := XR_trans _ _ _ _ _ _ _ _ _ _ k277 (XTop.xrun_seg_sound XCuts.z278 XCuts.b278 XCuts.z279 XCuts.b279 XCuts.n278 XCuts.v278 eq_refl XJ0278.seg).
Definition k279 := XR_trans _ _ _ _ _ _ _ _ _ _ k278 (XTop.xrun_seg_sound XCuts.z279 XCuts.b279 XCuts.z280 XCuts.b280 XCuts.n279 XCuts.v279 eq_refl XJ0279.seg).
Definition k280 := XR_trans _ _ _ _ _ _ _ _ _ _ k279 (XTop.xrun_seg_sound XCuts.z280 XCuts.b280 XCuts.z281 XCuts.b281 XCuts.n280 XCuts.v280 eq_refl XJ0280.seg).
Definition k281 := XR_trans _ _ _ _ _ _ _ _ _ _ k280 (XTop.xrun_seg_sound XCuts.z281 XCuts.b281 XCuts.z282 XCuts.b282 XCuts.n281 XCuts.v281 eq_refl XJ0281.seg).
Definition k282 := XR_trans _ _ _ _ _ _ _ _ _ _ k281 (XTop.xrun_seg_sound XCuts.z282 XCuts.b282 XCuts.z283 XCuts.b283 XCuts.n282 XCuts.v282 eq_refl XJ0282.seg).
Definition k283 := XR_trans _ _ _ _ _ _ _ _ _ _ k282 (XTop.xrun_seg_sound XCuts.z283 XCuts.b283 XCuts.z284 XCuts.b284 XCuts.n283 XCuts.v283 eq_refl XJ0283.seg).
Definition k284 := XR_trans _ _ _ _ _ _ _ _ _ _ k283 (XTop.xrun_seg_sound XCuts.z284 XCuts.b284 XCuts.z285 XCuts.b285 XCuts.n284 XCuts.v284 eq_refl XJ0284.seg).
Definition k285 := XR_trans _ _ _ _ _ _ _ _ _ _ k284 (XTop.xrun_seg_sound XCuts.z285 XCuts.b285 XCuts.z286 XCuts.b286 XCuts.n285 XCuts.v285 eq_refl XJ0285.seg).
Definition k286 := XR_trans _ _ _ _ _ _ _ _ _ _ k285 (XTop.xrun_seg_sound XCuts.z286 XCuts.b286 XCuts.z287 XCuts.b287 XCuts.n286 XCuts.v286 eq_refl XJ0286.seg).
Definition k287 := XR_trans _ _ _ _ _ _ _ _ _ _ k286 (XTop.xrun_seg_sound XCuts.z287 XCuts.b287 XCuts.z288 XCuts.b288 XCuts.n287 XCuts.v287 eq_refl XJ0287.seg).
Definition k288 := XR_trans _ _ _ _ _ _ _ _ _ _ k287 (XTop.xrun_seg_sound XCuts.z288 XCuts.b288 XCuts.z289 XCuts.b289 XCuts.n288 XCuts.v288 eq_refl XJ0288.seg).
Definition k289 := XR_trans _ _ _ _ _ _ _ _ _ _ k288 (XTop.xrun_seg_sound XCuts.z289 XCuts.b289 XCuts.z290 XCuts.b290 XCuts.n289 XCuts.v289 eq_refl XJ0289.seg).
Definition k290 := XR_trans _ _ _ _ _ _ _ _ _ _ k289 (XTop.xrun_seg_sound XCuts.z290 XCuts.b290 XCuts.z291 XCuts.b291 XCuts.n290 XCuts.v290 eq_refl XJ0290.seg).
Definition k291 := XR_trans _ _ _ _ _ _ _ _ _ _ k290 (XTop.xrun_seg_sound XCuts.z291 XCuts.b291 XCuts.z292 XCuts.b292 XCuts.n291 XCuts.v291 eq_refl XJ0291.seg).
Definition k292 := XR_trans _ _ _ _ _ _ _ _ _ _ k291 (XTop.xrun_seg_sound XCuts.z292 XCuts.b292 XCuts.z293 XCuts.b293 XCuts.n292 XCuts.v292 eq_refl XJ0292.seg).
Definition k293 := XR_trans _ _ _ _ _ _ _ _ _ _ k292 (XTop.xrun_seg_sound XCuts.z293 XCuts.b293 XCuts.z294 XCuts.b294 XCuts.n293 XCuts.v293 eq_refl XJ0293.seg).
Definition k294 := XR_trans _ _ _ _ _ _ _ _ _ _ k293 (XTop.xrun_seg_sound XCuts.z294 XCuts.b294 XCuts.z295 XCuts.b295 XCuts.n294 XCuts.v294 eq_refl XJ0294.seg).
Definition k295 := XR_trans _ _ _ _ _ _ _ _ _ _ k294 (XTop.xrun_seg_sound XCuts.z295 XCuts.b295 XCuts.z296 XCuts.b296 XCuts.n295 XCuts.v295 eq_refl XJ0295.seg).
Definition k296 := XR_trans _ _ _ _ _ _ _ _ _ _ k295 (XTop.xrun_seg_sound XCuts.z296 XCuts.b296 XCuts.z297 XCuts.b297 XCuts.n296 XCuts.v296 eq_refl XJ0296.seg).
Definition k297 := XR_trans _ _ _ _ _ _ _ _ _ _ k296 (XTop.xrun_seg_sound XCuts.z297 XCuts.b297 XCuts.z298 XCuts.b298 XCuts.n297 XCuts.v297 eq_refl XJ0297.seg).
Definition k298 := XR_trans _ _ _ _ _ _ _ _ _ _ k297 (XTop.xrun_seg_sound XCuts.z298 XCuts.b298 XCuts.z299 XCuts.b299 XCuts.n298 XCuts.v298 eq_refl XJ0298.seg).
Definition k299 := XR_trans _ _ _ _ _ _ _ _ _ _ k298 (XTop.xrun_seg_sound XCuts.z299 XCuts.b299 XCuts.z300 XCuts.b300 XCuts.n299 XCuts.v299 eq_refl XJ0299.seg).
Definition k300 := XR_trans _ _ _ _ _ _ _ _ _ _ k299 (XTop.xrun_seg_sound XCuts.z300 XCuts.b300 XCuts.z301 XCuts.b301 XCuts.n300 XCuts.v300 eq_refl XJ0300.seg).
Definition k301 := XR_trans _ _ _ _ _ _ _ _ _ _ k300 (XTop.xrun_seg_sound XCuts.z301 XCuts.b301 XCuts.z302 XCuts.b302 XCuts.n301 XCuts.v301 eq_refl XJ0301.seg).
Definition k302 := XR_trans _ _ _ _ _ _ _ _ _ _ k301 (XTop.xrun_seg_sound XCuts.z302 XCuts.b302 XCuts.z303 XCuts.b303 XCuts.n302 XCuts.v302 eq_refl XJ0302.seg).
Definition k303 := XR_trans _ _ _ _ _ _ _ _ _ _ k302 (XTop.xrun_seg_sound XCuts.z303 XCuts.b303 XCuts.z304 XCuts.b304 XCuts.n303 XCuts.v303 eq_refl XJ0303.seg).
Definition k304 := XR_trans _ _ _ _ _ _ _ _ _ _ k303 (XTop.xrun_seg_sound XCuts.z304 XCuts.b304 XCuts.z305 XCuts.b305 XCuts.n304 XCuts.v304 eq_refl XJ0304.seg).
Definition k305 := XR_trans _ _ _ _ _ _ _ _ _ _ k304 (XTop.xrun_seg_sound XCuts.z305 XCuts.b305 XCuts.z306 XCuts.b306 XCuts.n305 XCuts.v305 eq_refl XJ0305.seg).
Definition k306 := XR_trans _ _ _ _ _ _ _ _ _ _ k305 (XTop.xrun_seg_sound XCuts.z306 XCuts.b306 XCuts.z307 XCuts.b307 XCuts.n306 XCuts.v306 eq_refl XJ0306.seg).
Definition k307 := XR_trans _ _ _ _ _ _ _ _ _ _ k306 (XTop.xrun_seg_sound XCuts.z307 XCuts.b307 XCuts.z308 XCuts.b308 XCuts.n307 XCuts.v307 eq_refl XJ0307.seg).
Definition k308 := XR_trans _ _ _ _ _ _ _ _ _ _ k307 (XTop.xrun_seg_sound XCuts.z308 XCuts.b308 XCuts.z309 XCuts.b309 XCuts.n308 XCuts.v308 eq_refl XJ0308.seg).
Definition k309 := XR_trans _ _ _ _ _ _ _ _ _ _ k308 (XTop.xrun_seg_sound XCuts.z309 XCuts.b309 XCuts.z310 XCuts.b310 XCuts.n309 XCuts.v309 eq_refl XJ0309.seg).
Definition k310 := XR_trans _ _ _ _ _ _ _ _ _ _ k309 (XTop.xrun_seg_sound XCuts.z310 XCuts.b310 XCuts.z311 XCuts.b311 XCuts.n310 XCuts.v310 eq_refl XJ0310.seg).
Definition k311 := XR_trans _ _ _ _ _ _ _ _ _ _ k310 (XTop.xrun_seg_sound XCuts.z311 XCuts.b311 XCuts.z312 XCuts.b312 XCuts.n311 XCuts.v311 eq_refl XJ0311.seg).
Definition k312 := XR_trans _ _ _ _ _ _ _ _ _ _ k311 (XTop.xrun_seg_sound XCuts.z312 XCuts.b312 XCuts.z313 XCuts.b313 XCuts.n312 XCuts.v312 eq_refl XJ0312.seg).
Definition k313 := XR_trans _ _ _ _ _ _ _ _ _ _ k312 (XTop.xrun_seg_sound XCuts.z313 XCuts.b313 XCuts.z314 XCuts.b314 XCuts.n313 XCuts.v313 eq_refl XJ0313.seg).
Definition k314 := XR_trans _ _ _ _ _ _ _ _ _ _ k313 (XTop.xrun_seg_sound XCuts.z314 XCuts.b314 XCuts.z315 XCuts.b315 XCuts.n314 XCuts.v314 eq_refl XJ0314.seg).
Definition k315 := XR_trans _ _ _ _ _ _ _ _ _ _ k314 (XTop.xrun_seg_sound XCuts.z315 XCuts.b315 XCuts.z316 XCuts.b316 XCuts.n315 XCuts.v315 eq_refl XJ0315.seg).
Definition k316 := XR_trans _ _ _ _ _ _ _ _ _ _ k315 (XTop.xrun_seg_sound XCuts.z316 XCuts.b316 XCuts.z317 XCuts.b317 XCuts.n316 XCuts.v316 eq_refl XJ0316.seg).
Definition k317 := XR_trans _ _ _ _ _ _ _ _ _ _ k316 (XTop.xrun_seg_sound XCuts.z317 XCuts.b317 XCuts.z318 XCuts.b318 XCuts.n317 XCuts.v317 eq_refl XJ0317.seg).
Definition k318 := XR_trans _ _ _ _ _ _ _ _ _ _ k317 (XTop.xrun_seg_sound XCuts.z318 XCuts.b318 XCuts.z319 XCuts.b319 XCuts.n318 XCuts.v318 eq_refl XJ0318.seg).
Definition k319 := XR_trans _ _ _ _ _ _ _ _ _ _ k318 (XTop.xrun_seg_sound XCuts.z319 XCuts.b319 XCuts.z320 XCuts.b320 XCuts.n319 XCuts.v319 eq_refl XJ0319.seg).
Definition k320 := XR_trans _ _ _ _ _ _ _ _ _ _ k319 (XTop.xrun_seg_sound XCuts.z320 XCuts.b320 XCuts.z321 XCuts.b321 XCuts.n320 XCuts.v320 eq_refl XJ0320.seg).
Definition k321 := XR_trans _ _ _ _ _ _ _ _ _ _ k320 (XTop.xrun_seg_sound XCuts.z321 XCuts.b321 XCuts.z322 XCuts.b322 XCuts.n321 XCuts.v321 eq_refl XJ0321.seg).
Definition k322 := XR_trans _ _ _ _ _ _ _ _ _ _ k321 (XTop.xrun_seg_sound XCuts.z322 XCuts.b322 XCuts.z323 XCuts.b323 XCuts.n322 XCuts.v322 eq_refl XJ0322.seg).
Definition k323 := XR_trans _ _ _ _ _ _ _ _ _ _ k322 (XTop.xrun_seg_sound XCuts.z323 XCuts.b323 XCuts.z324 XCuts.b324 XCuts.n323 XCuts.v323 eq_refl XJ0323.seg).
Definition k324 := XR_trans _ _ _ _ _ _ _ _ _ _ k323 (XTop.xrun_seg_sound XCuts.z324 XCuts.b324 XCuts.z325 XCuts.b325 XCuts.n324 XCuts.v324 eq_refl XJ0324.seg).
Definition k325 := XR_trans _ _ _ _ _ _ _ _ _ _ k324 (XTop.xrun_seg_sound XCuts.z325 XCuts.b325 XCuts.z326 XCuts.b326 XCuts.n325 XCuts.v325 eq_refl XJ0325.seg).
Definition k326 := XR_trans _ _ _ _ _ _ _ _ _ _ k325 (XTop.xrun_seg_sound XCuts.z326 XCuts.b326 XCuts.z327 XCuts.b327 XCuts.n326 XCuts.v326 eq_refl XJ0326.seg).
Definition k327 := XR_trans _ _ _ _ _ _ _ _ _ _ k326 (XTop.xrun_seg_sound XCuts.z327 XCuts.b327 XCuts.z328 XCuts.b328 XCuts.n327 XCuts.v327 eq_refl XJ0327.seg).
Definition k328 := XR_trans _ _ _ _ _ _ _ _ _ _ k327 (XTop.xrun_seg_sound XCuts.z328 XCuts.b328 XCuts.z329 XCuts.b329 XCuts.n328 XCuts.v328 eq_refl XJ0328.seg).
Definition k329 := XR_trans _ _ _ _ _ _ _ _ _ _ k328 (XTop.xrun_seg_sound XCuts.z329 XCuts.b329 XCuts.z330 XCuts.b330 XCuts.n329 XCuts.v329 eq_refl XJ0329.seg).
Definition k330 := XR_trans _ _ _ _ _ _ _ _ _ _ k329 (XTop.xrun_seg_sound XCuts.z330 XCuts.b330 XCuts.z331 XCuts.b331 XCuts.n330 XCuts.v330 eq_refl XJ0330.seg).
Definition k331 := XR_trans _ _ _ _ _ _ _ _ _ _ k330 (XTop.xrun_seg_sound XCuts.z331 XCuts.b331 XCuts.z332 XCuts.b332 XCuts.n331 XCuts.v331 eq_refl XJ0331.seg).
Definition k332 := XR_trans _ _ _ _ _ _ _ _ _ _ k331 (XTop.xrun_seg_sound XCuts.z332 XCuts.b332 XCuts.z333 XCuts.b333 XCuts.n332 XCuts.v332 eq_refl XJ0332.seg).
Definition k333 := XR_trans _ _ _ _ _ _ _ _ _ _ k332 (XTop.xrun_seg_sound XCuts.z333 XCuts.b333 XCuts.z334 XCuts.b334 XCuts.n333 XCuts.v333 eq_refl XJ0333.seg).
Definition k334 := XR_trans _ _ _ _ _ _ _ _ _ _ k333 (XTop.xrun_seg_sound XCuts.z334 XCuts.b334 XCuts.z335 XCuts.b335 XCuts.n334 XCuts.v334 eq_refl XJ0334.seg).
Definition k335 := XR_trans _ _ _ _ _ _ _ _ _ _ k334 (XTop.xrun_seg_sound XCuts.z335 XCuts.b335 XCuts.z336 XCuts.b336 XCuts.n335 XCuts.v335 eq_refl XJ0335.seg).
Definition k336 := XR_trans _ _ _ _ _ _ _ _ _ _ k335 (XTop.xrun_seg_sound XCuts.z336 XCuts.b336 XCuts.z337 XCuts.b337 XCuts.n336 XCuts.v336 eq_refl XJ0336.seg).
Definition k337 := XR_trans _ _ _ _ _ _ _ _ _ _ k336 (XTop.xrun_seg_sound XCuts.z337 XCuts.b337 XCuts.z338 XCuts.b338 XCuts.n337 XCuts.v337 eq_refl XJ0337.seg).
Definition k338 := XR_trans _ _ _ _ _ _ _ _ _ _ k337 (XTop.xrun_seg_sound XCuts.z338 XCuts.b338 XCuts.z339 XCuts.b339 XCuts.n338 XCuts.v338 eq_refl XJ0338.seg).
Definition k339 := XR_trans _ _ _ _ _ _ _ _ _ _ k338 (XTop.xrun_seg_sound XCuts.z339 XCuts.b339 XCuts.z340 XCuts.b340 XCuts.n339 XCuts.v339 eq_refl XJ0339.seg).
Definition k340 := XR_trans _ _ _ _ _ _ _ _ _ _ k339 (XTop.xrun_seg_sound XCuts.z340 XCuts.b340 XCuts.z341 XCuts.b341 XCuts.n340 XCuts.v340 eq_refl XJ0340.seg).
Definition k341 := XR_trans _ _ _ _ _ _ _ _ _ _ k340 (XTop.xrun_seg_sound XCuts.z341 XCuts.b341 XCuts.z342 XCuts.b342 XCuts.n341 XCuts.v341 eq_refl XJ0341.seg).
Definition k342 := XR_trans _ _ _ _ _ _ _ _ _ _ k341 (XTop.xrun_seg_sound XCuts.z342 XCuts.b342 XCuts.z343 XCuts.b343 XCuts.n342 XCuts.v342 eq_refl XJ0342.seg).
Definition k343 := XR_trans _ _ _ _ _ _ _ _ _ _ k342 (XTop.xrun_seg_sound XCuts.z343 XCuts.b343 XCuts.z344 XCuts.b344 XCuts.n343 XCuts.v343 eq_refl XJ0343.seg).
Definition k344 := XR_trans _ _ _ _ _ _ _ _ _ _ k343 (XTop.xrun_seg_sound XCuts.z344 XCuts.b344 XCuts.z345 XCuts.b345 XCuts.n344 XCuts.v344 eq_refl XJ0344.seg).
Definition k345 := XR_trans _ _ _ _ _ _ _ _ _ _ k344 (XTop.xrun_seg_sound XCuts.z345 XCuts.b345 XCuts.z346 XCuts.b346 XCuts.n345 XCuts.v345 eq_refl XJ0345.seg).
Definition k346 := XR_trans _ _ _ _ _ _ _ _ _ _ k345 (XTop.xrun_seg_sound XCuts.z346 XCuts.b346 XCuts.z347 XCuts.b347 XCuts.n346 XCuts.v346 eq_refl XJ0346.seg).
Definition k347 := XR_trans _ _ _ _ _ _ _ _ _ _ k346 (XTop.xrun_seg_sound XCuts.z347 XCuts.b347 XCuts.z348 XCuts.b348 XCuts.n347 XCuts.v347 eq_refl XJ0347.seg).
Definition k348 := XR_trans _ _ _ _ _ _ _ _ _ _ k347 (XTop.xrun_seg_sound XCuts.z348 XCuts.b348 XCuts.z349 XCuts.b349 XCuts.n348 XCuts.v348 eq_refl XJ0348.seg).
Definition k349 := XR_trans _ _ _ _ _ _ _ _ _ _ k348 (XTop.xrun_seg_sound XCuts.z349 XCuts.b349 XCuts.z350 XCuts.b350 XCuts.n349 XCuts.v349 eq_refl XJ0349.seg).
Definition k350 := XR_trans _ _ _ _ _ _ _ _ _ _ k349 (XTop.xrun_seg_sound XCuts.z350 XCuts.b350 XCuts.z351 XCuts.b351 XCuts.n350 XCuts.v350 eq_refl XJ0350.seg).
Definition k351 := XR_trans _ _ _ _ _ _ _ _ _ _ k350 (XTop.xrun_seg_sound XCuts.z351 XCuts.b351 XCuts.z352 XCuts.b352 XCuts.n351 XCuts.v351 eq_refl XJ0351.seg).
Definition k352 := XR_trans _ _ _ _ _ _ _ _ _ _ k351 (XTop.xrun_seg_sound XCuts.z352 XCuts.b352 XCuts.z353 XCuts.b353 XCuts.n352 XCuts.v352 eq_refl XJ0352.seg).
Definition k353 := XR_trans _ _ _ _ _ _ _ _ _ _ k352 (XTop.xrun_seg_sound XCuts.z353 XCuts.b353 XCuts.z354 XCuts.b354 XCuts.n353 XCuts.v353 eq_refl XJ0353.seg).
Definition k354 := XR_trans _ _ _ _ _ _ _ _ _ _ k353 (XTop.xrun_seg_sound XCuts.z354 XCuts.b354 XCuts.z355 XCuts.b355 XCuts.n354 XCuts.v354 eq_refl XJ0354.seg).
Definition k355 := XR_trans _ _ _ _ _ _ _ _ _ _ k354 (XTop.xrun_seg_sound XCuts.z355 XCuts.b355 XCuts.z356 XCuts.b356 XCuts.n355 XCuts.v355 eq_refl XJ0355.seg).
Definition k356 := XR_trans _ _ _ _ _ _ _ _ _ _ k355 (XTop.xrun_seg_sound XCuts.z356 XCuts.b356 XCuts.z357 XCuts.b357 XCuts.n356 XCuts.v356 eq_refl XJ0356.seg).
Definition k357 := XR_trans _ _ _ _ _ _ _ _ _ _ k356 (XTop.xrun_seg_sound XCuts.z357 XCuts.b357 XCuts.z358 XCuts.b358 XCuts.n357 XCuts.v357 eq_refl XJ0357.seg).
Definition k358 := XR_trans _ _ _ _ _ _ _ _ _ _ k357 (XTop.xrun_seg_sound XCuts.z358 XCuts.b358 XCuts.z359 XCuts.b359 XCuts.n358 XCuts.v358 eq_refl XJ0358.seg).
Definition k359 := XR_trans _ _ _ _ _ _ _ _ _ _ k358 (XTop.xrun_seg_sound XCuts.z359 XCuts.b359 XCuts.z360 XCuts.b360 XCuts.n359 XCuts.v359 eq_refl XJ0359.seg).
Definition k360 := XR_trans _ _ _ _ _ _ _ _ _ _ k359 (XTop.xrun_seg_sound XCuts.z360 XCuts.b360 XCuts.z361 XCuts.b361 XCuts.n360 XCuts.v360 eq_refl XJ0360.seg).
Definition k361 := XR_trans _ _ _ _ _ _ _ _ _ _ k360 (XTop.xrun_seg_sound XCuts.z361 XCuts.b361 XCuts.z362 XCuts.b362 XCuts.n361 XCuts.v361 eq_refl XJ0361.seg).
Definition k362 := XR_trans _ _ _ _ _ _ _ _ _ _ k361 (XTop.xrun_seg_sound XCuts.z362 XCuts.b362 XCuts.z363 XCuts.b363 XCuts.n362 XCuts.v362 eq_refl XJ0362.seg).
Definition k363 := XR_trans _ _ _ _ _ _ _ _ _ _ k362 (XTop.xrun_seg_sound XCuts.z363 XCuts.b363 XCuts.z364 XCuts.b364 XCuts.n363 XCuts.v363 eq_refl XJ0363.seg).
Definition k364 := XR_trans _ _ _ _ _ _ _ _ _ _ k363 (XTop.xrun_seg_sound XCuts.z364 XCuts.b364 XCuts.z365 XCuts.b365 XCuts.n364 XCuts.v364 eq_refl XJ0364.seg).
Definition k365 := XR_trans _ _ _ _ _ _ _ _ _ _ k364 (XTop.xrun_seg_sound XCuts.z365 XCuts.b365 XCuts.z366 XCuts.b366 XCuts.n365 XCuts.v365 eq_refl XJ0365.seg).
Definition k366 := XR_trans _ _ _ _ _ _ _ _ _ _ k365 (XTop.xrun_seg_sound XCuts.z366 XCuts.b366 XCuts.z367 XCuts.b367 XCuts.n366 XCuts.v366 eq_refl XJ0366.seg).
Definition k367 := XR_trans _ _ _ _ _ _ _ _ _ _ k366 (XTop.xrun_seg_sound XCuts.z367 XCuts.b367 XCuts.z368 XCuts.b368 XCuts.n367 XCuts.v367 eq_refl XJ0367.seg).
Definition k368 := XR_trans _ _ _ _ _ _ _ _ _ _ k367 (XTop.xrun_seg_sound XCuts.z368 XCuts.b368 XCuts.z369 XCuts.b369 XCuts.n368 XCuts.v368 eq_refl XJ0368.seg).
Definition k369 := XR_trans _ _ _ _ _ _ _ _ _ _ k368 (XTop.xrun_seg_sound XCuts.z369 XCuts.b369 XCuts.z370 XCuts.b370 XCuts.n369 XCuts.v369 eq_refl XJ0369.seg).
Definition k370 := XR_trans _ _ _ _ _ _ _ _ _ _ k369 (XTop.xrun_seg_sound XCuts.z370 XCuts.b370 XCuts.z371 XCuts.b371 XCuts.n370 XCuts.v370 eq_refl XJ0370.seg).
Definition k371 := XR_trans _ _ _ _ _ _ _ _ _ _ k370 (XTop.xrun_seg_sound XCuts.z371 XCuts.b371 XCuts.z372 XCuts.b372 XCuts.n371 XCuts.v371 eq_refl XJ0371.seg).
Definition k372 := XR_trans _ _ _ _ _ _ _ _ _ _ k371 (XTop.xrun_seg_sound XCuts.z372 XCuts.b372 XCuts.z373 XCuts.b373 XCuts.n372 XCuts.v372 eq_refl XJ0372.seg).
Definition k373 := XR_trans _ _ _ _ _ _ _ _ _ _ k372 (XTop.xrun_seg_sound XCuts.z373 XCuts.b373 XCuts.z374 XCuts.b374 XCuts.n373 XCuts.v373 eq_refl XJ0373.seg).
Definition k374 := XR_trans _ _ _ _ _ _ _ _ _ _ k373 (XTop.xrun_seg_sound XCuts.z374 XCuts.b374 XCuts.z375 XCuts.b375 XCuts.n374 XCuts.v374 eq_refl XJ0374.seg).
Definition k375 := XR_trans _ _ _ _ _ _ _ _ _ _ k374 (XTop.xrun_seg_sound XCuts.z375 XCuts.b375 XCuts.z376 XCuts.b376 XCuts.n375 XCuts.v375 eq_refl XJ0375.seg).
Definition k376 := XR_trans _ _ _ _ _ _ _ _ _ _ k375 (XTop.xrun_seg_sound XCuts.z376 XCuts.b376 XCuts.z377 XCuts.b377 XCuts.n376 XCuts.v376 eq_refl XJ0376.seg).
Definition k377 := XR_trans _ _ _ _ _ _ _ _ _ _ k376 (XTop.xrun_seg_sound XCuts.z377 XCuts.b377 XCuts.z378 XCuts.b378 XCuts.n377 XCuts.v377 eq_refl XJ0377.seg).
Definition k378 := XR_trans _ _ _ _ _ _ _ _ _ _ k377 (XTop.xrun_seg_sound XCuts.z378 XCuts.b378 XCuts.z379 XCuts.b379 XCuts.n378 XCuts.v378 eq_refl XJ0378.seg).
Definition k379 := XR_trans _ _ _ _ _ _ _ _ _ _ k378 (XTop.xrun_seg_sound XCuts.z379 XCuts.b379 XCuts.z380 XCuts.b380 XCuts.n379 XCuts.v379 eq_refl XJ0379.seg).
Definition k380 := XR_trans _ _ _ _ _ _ _ _ _ _ k379 (XTop.xrun_seg_sound XCuts.z380 XCuts.b380 XCuts.z381 XCuts.b381 XCuts.n380 XCuts.v380 eq_refl XJ0380.seg).
Definition k381 := XR_trans _ _ _ _ _ _ _ _ _ _ k380 (XTop.xrun_seg_sound XCuts.z381 XCuts.b381 XCuts.z382 XCuts.b382 XCuts.n381 XCuts.v381 eq_refl XJ0381.seg).
Definition k382 := XR_trans _ _ _ _ _ _ _ _ _ _ k381 (XTop.xrun_seg_sound XCuts.z382 XCuts.b382 XCuts.z383 XCuts.b383 XCuts.n382 XCuts.v382 eq_refl XJ0382.seg).
Definition k383 := XR_trans _ _ _ _ _ _ _ _ _ _ k382 (XTop.xrun_seg_sound XCuts.z383 XCuts.b383 XCuts.z384 XCuts.b384 XCuts.n383 XCuts.v383 eq_refl XJ0383.seg).
Definition k384 := XR_trans _ _ _ _ _ _ _ _ _ _ k383 (XTop.xrun_seg_sound XCuts.z384 XCuts.b384 XCuts.z385 XCuts.b385 XCuts.n384 XCuts.v384 eq_refl XJ0384.seg).
Definition k385 := XR_trans _ _ _ _ _ _ _ _ _ _ k384 (XTop.xrun_seg_sound XCuts.z385 XCuts.b385 XCuts.z386 XCuts.b386 XCuts.n385 XCuts.v385 eq_refl XJ0385.seg).
Definition k386 := XR_trans _ _ _ _ _ _ _ _ _ _ k385 (XTop.xrun_seg_sound XCuts.z386 XCuts.b386 XCuts.z387 XCuts.b387 XCuts.n386 XCuts.v386 eq_refl XJ0386.seg).
Definition k387 := XR_trans _ _ _ _ _ _ _ _ _ _ k386 (XTop.xrun_seg_sound XCuts.z387 XCuts.b387 XCuts.z388 XCuts.b388 XCuts.n387 XCuts.v387 eq_refl XJ0387.seg).
Definition k388 := XR_trans _ _ _ _ _ _ _ _ _ _ k387 (XTop.xrun_seg_sound XCuts.z388 XCuts.b388 XCuts.z389 XCuts.b389 XCuts.n388 XCuts.v388 eq_refl XJ0388.seg).
Definition k389 := XR_trans _ _ _ _ _ _ _ _ _ _ k388 (XTop.xrun_seg_sound XCuts.z389 XCuts.b389 XCuts.z390 XCuts.b390 XCuts.n389 XCuts.v389 eq_refl XJ0389.seg).
Definition k390 := XR_trans _ _ _ _ _ _ _ _ _ _ k389 (XTop.xrun_seg_sound XCuts.z390 XCuts.b390 XCuts.z391 XCuts.b391 XCuts.n390 XCuts.v390 eq_refl XJ0390.seg).
Definition k391 := XR_trans _ _ _ _ _ _ _ _ _ _ k390 (XTop.xrun_seg_sound XCuts.z391 XCuts.b391 XCuts.z392 XCuts.b392 XCuts.n391 XCuts.v391 eq_refl XJ0391.seg).
Definition k392 := XR_trans _ _ _ _ _ _ _ _ _ _ k391 (XTop.xrun_seg_sound XCuts.z392 XCuts.b392 XCuts.z393 XCuts.b393 XCuts.n392 XCuts.v392 eq_refl XJ0392.seg).
Definition k393 := XR_trans _ _ _ _ _ _ _ _ _ _ k392 (XTop.xrun_seg_sound XCuts.z393 XCuts.b393 XCuts.z394 XCuts.b394 XCuts.n393 XCuts.v393 eq_refl XJ0393.seg).
Definition k394 := XR_trans _ _ _ _ _ _ _ _ _ _ k393 (XTop.xrun_seg_sound XCuts.z394 XCuts.b394 XCuts.z395 XCuts.b395 XCuts.n394 XCuts.v394 eq_refl XJ0394.seg).
Definition k395 := XR_trans _ _ _ _ _ _ _ _ _ _ k394 (XTop.xrun_seg_sound XCuts.z395 XCuts.b395 XCuts.z396 XCuts.b396 XCuts.n395 XCuts.v395 eq_refl XJ0395.seg).
Definition k396 := XR_trans _ _ _ _ _ _ _ _ _ _ k395 (XTop.xrun_seg_sound XCuts.z396 XCuts.b396 XCuts.z397 XCuts.b397 XCuts.n396 XCuts.v396 eq_refl XJ0396.seg).
Definition k397 := XR_trans _ _ _ _ _ _ _ _ _ _ k396 (XTop.xrun_seg_sound XCuts.z397 XCuts.b397 XCuts.z398 XCuts.b398 XCuts.n397 XCuts.v397 eq_refl XJ0397.seg).
Definition k398 := XR_trans _ _ _ _ _ _ _ _ _ _ k397 (XTop.xrun_seg_sound XCuts.z398 XCuts.b398 XCuts.z399 XCuts.b399 XCuts.n398 XCuts.v398 eq_refl XJ0398.seg).
Definition k399 := XR_trans _ _ _ _ _ _ _ _ _ _ k398 (XTop.xrun_seg_sound XCuts.z399 XCuts.b399 XCuts.z400 XCuts.b400 XCuts.n399 XCuts.v399 eq_refl XJ0399.seg).
Definition k400 := XR_trans _ _ _ _ _ _ _ _ _ _ k399 (XTop.xrun_seg_sound XCuts.z400 XCuts.b400 XCuts.z401 XCuts.b401 XCuts.n400 XCuts.v400 eq_refl XJ0400.seg).
Definition k401 := XR_trans _ _ _ _ _ _ _ _ _ _ k400 (XTop.xrun_seg_sound XCuts.z401 XCuts.b401 XCuts.z402 XCuts.b402 XCuts.n401 XCuts.v401 eq_refl XJ0401.seg).
Definition k402 := XR_trans _ _ _ _ _ _ _ _ _ _ k401 (XTop.xrun_seg_sound XCuts.z402 XCuts.b402 XCuts.z403 XCuts.b403 XCuts.n402 XCuts.v402 eq_refl XJ0402.seg).
Definition k403 := XR_trans _ _ _ _ _ _ _ _ _ _ k402 (XTop.xrun_seg_sound XCuts.z403 XCuts.b403 XCuts.z404 XCuts.b404 XCuts.n403 XCuts.v403 eq_refl XJ0403.seg).
Definition k404 := XR_trans _ _ _ _ _ _ _ _ _ _ k403 (XTop.xrun_seg_sound XCuts.z404 XCuts.b404 XCuts.z405 XCuts.b405 XCuts.n404 XCuts.v404 eq_refl XJ0404.seg).
Definition k405 := XR_trans _ _ _ _ _ _ _ _ _ _ k404 (XTop.xrun_seg_sound XCuts.z405 XCuts.b405 XCuts.z406 XCuts.b406 XCuts.n405 XCuts.v405 eq_refl XJ0405.seg).
Definition k406 := XR_trans _ _ _ _ _ _ _ _ _ _ k405 (XTop.xrun_seg_sound XCuts.z406 XCuts.b406 XCuts.z407 XCuts.b407 XCuts.n406 XCuts.v406 eq_refl XJ0406.seg).
Definition k407 := XR_trans _ _ _ _ _ _ _ _ _ _ k406 (XTop.xrun_seg_sound XCuts.z407 XCuts.b407 XCuts.z408 XCuts.b408 XCuts.n407 XCuts.v407 eq_refl XJ0407.seg).
Definition k408 := XR_trans _ _ _ _ _ _ _ _ _ _ k407 (XTop.xrun_seg_sound XCuts.z408 XCuts.b408 XCuts.z409 XCuts.b409 XCuts.n408 XCuts.v408 eq_refl XJ0408.seg).
Definition k409 := XR_trans _ _ _ _ _ _ _ _ _ _ k408 (XTop.xrun_seg_sound XCuts.z409 XCuts.b409 XCuts.z410 XCuts.b410 XCuts.n409 XCuts.v409 eq_refl XJ0409.seg).
Definition k410 := XR_trans _ _ _ _ _ _ _ _ _ _ k409 (XTop.xrun_seg_sound XCuts.z410 XCuts.b410 XCuts.z411 XCuts.b411 XCuts.n410 XCuts.v410 eq_refl XJ0410.seg).
Definition k411 := XR_trans _ _ _ _ _ _ _ _ _ _ k410 (XTop.xrun_seg_sound XCuts.z411 XCuts.b411 XCuts.z412 XCuts.b412 XCuts.n411 XCuts.v411 eq_refl XJ0411.seg).
Definition k412 := XR_trans _ _ _ _ _ _ _ _ _ _ k411 (XTop.xrun_seg_sound XCuts.z412 XCuts.b412 XCuts.z413 XCuts.b413 XCuts.n412 XCuts.v412 eq_refl XJ0412.seg).
Definition k413 := XR_trans _ _ _ _ _ _ _ _ _ _ k412 (XTop.xrun_seg_sound XCuts.z413 XCuts.b413 XCuts.z414 XCuts.b414 XCuts.n413 XCuts.v413 eq_refl XJ0413.seg).
Definition k414 := XR_trans _ _ _ _ _ _ _ _ _ _ k413 (XTop.xrun_seg_sound XCuts.z414 XCuts.b414 XCuts.z415 XCuts.b415 XCuts.n414 XCuts.v414 eq_refl XJ0414.seg).
Definition k415 := XR_trans _ _ _ _ _ _ _ _ _ _ k414 (XTop.xrun_seg_sound XCuts.z415 XCuts.b415 XCuts.z416 XCuts.b416 XCuts.n415 XCuts.v415 eq_refl XJ0415.seg).
Definition k416 := XR_trans _ _ _ _ _ _ _ _ _ _ k415 (XTop.xrun_seg_sound XCuts.z416 XCuts.b416 XCuts.z417 XCuts.b417 XCuts.n416 XCuts.v416 eq_refl XJ0416.seg).
Definition k417 := XR_trans _ _ _ _ _ _ _ _ _ _ k416 (XTop.xrun_seg_sound XCuts.z417 XCuts.b417 XCuts.z418 XCuts.b418 XCuts.n417 XCuts.v417 eq_refl XJ0417.seg).
Definition k418 := XR_trans _ _ _ _ _ _ _ _ _ _ k417 (XTop.xrun_seg_sound XCuts.z418 XCuts.b418 XCuts.z419 XCuts.b419 XCuts.n418 XCuts.v418 eq_refl XJ0418.seg).
Definition k419 := XR_trans _ _ _ _ _ _ _ _ _ _ k418 (XTop.xrun_seg_sound XCuts.z419 XCuts.b419 XCuts.z420 XCuts.b420 XCuts.n419 XCuts.v419 eq_refl XJ0419.seg).
Definition k420 := XR_trans _ _ _ _ _ _ _ _ _ _ k419 (XTop.xrun_seg_sound XCuts.z420 XCuts.b420 XCuts.z421 XCuts.b421 XCuts.n420 XCuts.v420 eq_refl XJ0420.seg).
Definition k421 := XR_trans _ _ _ _ _ _ _ _ _ _ k420 (XTop.xrun_seg_sound XCuts.z421 XCuts.b421 XCuts.z422 XCuts.b422 XCuts.n421 XCuts.v421 eq_refl XJ0421.seg).
Definition k422 := XR_trans _ _ _ _ _ _ _ _ _ _ k421 (XTop.xrun_seg_sound XCuts.z422 XCuts.b422 XCuts.z423 XCuts.b423 XCuts.n422 XCuts.v422 eq_refl XJ0422.seg).
Definition k423 := XR_trans _ _ _ _ _ _ _ _ _ _ k422 (XTop.xrun_seg_sound XCuts.z423 XCuts.b423 XCuts.z424 XCuts.b424 XCuts.n423 XCuts.v423 eq_refl XJ0423.seg).
Definition k424 := XR_trans _ _ _ _ _ _ _ _ _ _ k423 (XTop.xrun_seg_sound XCuts.z424 XCuts.b424 XCuts.z425 XCuts.b425 XCuts.n424 XCuts.v424 eq_refl XJ0424.seg).
Definition k425 := XR_trans _ _ _ _ _ _ _ _ _ _ k424 (XTop.xrun_seg_sound XCuts.z425 XCuts.b425 XCuts.z426 XCuts.b426 XCuts.n425 XCuts.v425 eq_refl XJ0425.seg).
Definition k426 := XR_trans _ _ _ _ _ _ _ _ _ _ k425 (XTop.xrun_seg_sound XCuts.z426 XCuts.b426 XCuts.z427 XCuts.b427 XCuts.n426 XCuts.v426 eq_refl XJ0426.seg).
Definition k427 := XR_trans _ _ _ _ _ _ _ _ _ _ k426 (XTop.xrun_seg_sound XCuts.z427 XCuts.b427 XCuts.z428 XCuts.b428 XCuts.n427 XCuts.v427 eq_refl XJ0427.seg).
Definition k428 := XR_trans _ _ _ _ _ _ _ _ _ _ k427 (XTop.xrun_seg_sound XCuts.z428 XCuts.b428 XCuts.z429 XCuts.b429 XCuts.n428 XCuts.v428 eq_refl XJ0428.seg).
Definition k429 := XR_trans _ _ _ _ _ _ _ _ _ _ k428 (XTop.xrun_seg_sound XCuts.z429 XCuts.b429 XCuts.z430 XCuts.b430 XCuts.n429 XCuts.v429 eq_refl XJ0429.seg).
Definition k430 := XR_trans _ _ _ _ _ _ _ _ _ _ k429 (XTop.xrun_seg_sound XCuts.z430 XCuts.b430 XCuts.z431 XCuts.b431 XCuts.n430 XCuts.v430 eq_refl XJ0430.seg).
Definition k431 := XR_trans _ _ _ _ _ _ _ _ _ _ k430 (XTop.xrun_seg_sound XCuts.z431 XCuts.b431 XCuts.z432 XCuts.b432 XCuts.n431 XCuts.v431 eq_refl XJ0431.seg).
Definition k432 := XR_trans _ _ _ _ _ _ _ _ _ _ k431 (XTop.xrun_seg_sound XCuts.z432 XCuts.b432 XCuts.z433 XCuts.b433 XCuts.n432 XCuts.v432 eq_refl XJ0432.seg).
Definition k433 := XR_trans _ _ _ _ _ _ _ _ _ _ k432 (XTop.xrun_seg_sound XCuts.z433 XCuts.b433 XCuts.z434 XCuts.b434 XCuts.n433 XCuts.v433 eq_refl XJ0433.seg).
Definition k434 := XR_trans _ _ _ _ _ _ _ _ _ _ k433 (XTop.xrun_seg_sound XCuts.z434 XCuts.b434 XCuts.z435 XCuts.b435 XCuts.n434 XCuts.v434 eq_refl XJ0434.seg).
Definition k435 := XR_trans _ _ _ _ _ _ _ _ _ _ k434 (XTop.xrun_seg_sound XCuts.z435 XCuts.b435 XCuts.z436 XCuts.b436 XCuts.n435 XCuts.v435 eq_refl XJ0435.seg).
Definition k436 := XR_trans _ _ _ _ _ _ _ _ _ _ k435 (XTop.xrun_seg_sound XCuts.z436 XCuts.b436 XCuts.z437 XCuts.b437 XCuts.n436 XCuts.v436 eq_refl XJ0436.seg).
Definition k437 := XR_trans _ _ _ _ _ _ _ _ _ _ k436 (XTop.xrun_seg_sound XCuts.z437 XCuts.b437 XCuts.z438 XCuts.b438 XCuts.n437 XCuts.v437 eq_refl XJ0437.seg).
Definition k438 := XR_trans _ _ _ _ _ _ _ _ _ _ k437 (XTop.xrun_seg_sound XCuts.z438 XCuts.b438 XCuts.z439 XCuts.b439 XCuts.n438 XCuts.v438 eq_refl XJ0438.seg).
Definition k439 := XR_trans _ _ _ _ _ _ _ _ _ _ k438 (XTop.xrun_seg_sound XCuts.z439 XCuts.b439 XCuts.z440 XCuts.b440 XCuts.n439 XCuts.v439 eq_refl XJ0439.seg).
Definition k440 := XR_trans _ _ _ _ _ _ _ _ _ _ k439 (XTop.xrun_seg_sound XCuts.z440 XCuts.b440 XCuts.z441 XCuts.b441 XCuts.n440 XCuts.v440 eq_refl XJ0440.seg).
Definition k441 := XR_trans _ _ _ _ _ _ _ _ _ _ k440 (XTop.xrun_seg_sound XCuts.z441 XCuts.b441 XCuts.z442 XCuts.b442 XCuts.n441 XCuts.v441 eq_refl XJ0441.seg).
Definition k442 := XR_trans _ _ _ _ _ _ _ _ _ _ k441 (XTop.xrun_seg_sound XCuts.z442 XCuts.b442 XCuts.z443 XCuts.b443 XCuts.n442 XCuts.v442 eq_refl XJ0442.seg).
Definition k443 := XR_trans _ _ _ _ _ _ _ _ _ _ k442 (XTop.xrun_seg_sound XCuts.z443 XCuts.b443 XCuts.z444 XCuts.b444 XCuts.n443 XCuts.v443 eq_refl XJ0443.seg).
Definition k444 := XR_trans _ _ _ _ _ _ _ _ _ _ k443 (XTop.xrun_seg_sound XCuts.z444 XCuts.b444 XCuts.z445 XCuts.b445 XCuts.n444 XCuts.v444 eq_refl XJ0444.seg).
Definition k445 := XR_trans _ _ _ _ _ _ _ _ _ _ k444 (XTop.xrun_seg_sound XCuts.z445 XCuts.b445 XCuts.z446 XCuts.b446 XCuts.n445 XCuts.v445 eq_refl XJ0445.seg).
Definition k446 := XR_trans _ _ _ _ _ _ _ _ _ _ k445 (XTop.xrun_seg_sound XCuts.z446 XCuts.b446 XCuts.z447 XCuts.b447 XCuts.n446 XCuts.v446 eq_refl XJ0446.seg).
Definition k447 := XR_trans _ _ _ _ _ _ _ _ _ _ k446 (XTop.xrun_seg_sound XCuts.z447 XCuts.b447 XCuts.z448 XCuts.b448 XCuts.n447 XCuts.v447 eq_refl XJ0447.seg).
Definition k448 := XR_trans _ _ _ _ _ _ _ _ _ _ k447 (XTop.xrun_seg_sound XCuts.z448 XCuts.b448 XCuts.z449 XCuts.b449 XCuts.n448 XCuts.v448 eq_refl XJ0448.seg).
Definition k449 := XR_trans _ _ _ _ _ _ _ _ _ _ k448 (XTop.xrun_seg_sound XCuts.z449 XCuts.b449 XCuts.z450 XCuts.b450 XCuts.n449 XCuts.v449 eq_refl XJ0449.seg).
Definition k450 := XR_trans _ _ _ _ _ _ _ _ _ _ k449 (XTop.xrun_seg_sound XCuts.z450 XCuts.b450 XCuts.z451 XCuts.b451 XCuts.n450 XCuts.v450 eq_refl XJ0450.seg).
Definition k451 := XR_trans _ _ _ _ _ _ _ _ _ _ k450 (XTop.xrun_seg_sound XCuts.z451 XCuts.b451 XCuts.z452 XCuts.b452 XCuts.n451 XCuts.v451 eq_refl XJ0451.seg).
Definition k452 := XR_trans _ _ _ _ _ _ _ _ _ _ k451 (XTop.xrun_seg_sound XCuts.z452 XCuts.b452 XCuts.z453 XCuts.b453 XCuts.n452 XCuts.v452 eq_refl XJ0452.seg).
Definition k453 := XR_trans _ _ _ _ _ _ _ _ _ _ k452 (XTop.xrun_seg_sound XCuts.z453 XCuts.b453 XCuts.z454 XCuts.b454 XCuts.n453 XCuts.v453 eq_refl XJ0453.seg).
Definition k454 := XR_trans _ _ _ _ _ _ _ _ _ _ k453 (XTop.xrun_seg_sound XCuts.z454 XCuts.b454 XCuts.z455 XCuts.b455 XCuts.n454 XCuts.v454 eq_refl XJ0454.seg).
Definition k455 := XR_trans _ _ _ _ _ _ _ _ _ _ k454 (XTop.xrun_seg_sound XCuts.z455 XCuts.b455 XCuts.z456 XCuts.b456 XCuts.n455 XCuts.v455 eq_refl XJ0455.seg).
Definition k456 := XR_trans _ _ _ _ _ _ _ _ _ _ k455 (XTop.xrun_seg_sound XCuts.z456 XCuts.b456 XCuts.z457 XCuts.b457 XCuts.n456 XCuts.v456 eq_refl XJ0456.seg).
Definition k457 := XR_trans _ _ _ _ _ _ _ _ _ _ k456 (XTop.xrun_seg_sound XCuts.z457 XCuts.b457 XCuts.z458 XCuts.b458 XCuts.n457 XCuts.v457 eq_refl XJ0457.seg).
Definition k458 := XR_trans _ _ _ _ _ _ _ _ _ _ k457 (XTop.xrun_seg_sound XCuts.z458 XCuts.b458 XCuts.z459 XCuts.b459 XCuts.n458 XCuts.v458 eq_refl XJ0458.seg).
Definition k459 := XR_trans _ _ _ _ _ _ _ _ _ _ k458 (XTop.xrun_seg_sound XCuts.z459 XCuts.b459 XCuts.z460 XCuts.b460 XCuts.n459 XCuts.v459 eq_refl XJ0459.seg).
Definition k460 := XR_trans _ _ _ _ _ _ _ _ _ _ k459 (XTop.xrun_seg_sound XCuts.z460 XCuts.b460 XCuts.z461 XCuts.b461 XCuts.n460 XCuts.v460 eq_refl XJ0460.seg).
Definition k461 := XR_trans _ _ _ _ _ _ _ _ _ _ k460 (XTop.xrun_seg_sound XCuts.z461 XCuts.b461 XCuts.z462 XCuts.b462 XCuts.n461 XCuts.v461 eq_refl XJ0461.seg).
Definition k462 := XR_trans _ _ _ _ _ _ _ _ _ _ k461 (XTop.xrun_seg_sound XCuts.z462 XCuts.b462 XCuts.z463 XCuts.b463 XCuts.n462 XCuts.v462 eq_refl XJ0462.seg).
Definition k463 := XR_trans _ _ _ _ _ _ _ _ _ _ k462 (XTop.xrun_seg_sound XCuts.z463 XCuts.b463 XCuts.z464 XCuts.b464 XCuts.n463 XCuts.v463 eq_refl XJ0463.seg).
Definition k464 := XR_trans _ _ _ _ _ _ _ _ _ _ k463 (XTop.xrun_seg_sound XCuts.z464 XCuts.b464 XCuts.z465 XCuts.b465 XCuts.n464 XCuts.v464 eq_refl XJ0464.seg).
Definition k465 := XR_trans _ _ _ _ _ _ _ _ _ _ k464 (XTop.xrun_seg_sound XCuts.z465 XCuts.b465 XCuts.z466 XCuts.b466 XCuts.n465 XCuts.v465 eq_refl XJ0465.seg).
Definition k466 := XR_trans _ _ _ _ _ _ _ _ _ _ k465 (XTop.xrun_seg_sound XCuts.z466 XCuts.b466 XCuts.z467 XCuts.b467 XCuts.n466 XCuts.v466 eq_refl XJ0466.seg).
Definition k467 := XR_trans _ _ _ _ _ _ _ _ _ _ k466 (XTop.xrun_seg_sound XCuts.z467 XCuts.b467 XCuts.z468 XCuts.b468 XCuts.n467 XCuts.v467 eq_refl XJ0467.seg).
Definition k468 := XR_trans _ _ _ _ _ _ _ _ _ _ k467 (XTop.xrun_seg_sound XCuts.z468 XCuts.b468 XCuts.z469 XCuts.b469 XCuts.n468 XCuts.v468 eq_refl XJ0468.seg).
Definition k469 := XR_trans _ _ _ _ _ _ _ _ _ _ k468 (XTop.xrun_seg_sound XCuts.z469 XCuts.b469 XCuts.z470 XCuts.b470 XCuts.n469 XCuts.v469 eq_refl XJ0469.seg).
Definition k470 := XR_trans _ _ _ _ _ _ _ _ _ _ k469 (XTop.xrun_seg_sound XCuts.z470 XCuts.b470 XCuts.z471 XCuts.b471 XCuts.n470 XCuts.v470 eq_refl XJ0470.seg).
Definition k471 := XR_trans _ _ _ _ _ _ _ _ _ _ k470 (XTop.xrun_seg_sound XCuts.z471 XCuts.b471 XCuts.z472 XCuts.b472 XCuts.n471 XCuts.v471 eq_refl XJ0471.seg).
Definition k472 := XR_trans _ _ _ _ _ _ _ _ _ _ k471 (XTop.xrun_seg_sound XCuts.z472 XCuts.b472 XCuts.z473 XCuts.b473 XCuts.n472 XCuts.v472 eq_refl XJ0472.seg).
Definition k473 := XR_trans _ _ _ _ _ _ _ _ _ _ k472 (XTop.xrun_seg_sound XCuts.z473 XCuts.b473 XCuts.z474 XCuts.b474 XCuts.n473 XCuts.v473 eq_refl XJ0473.seg).
Definition k474 := XR_trans _ _ _ _ _ _ _ _ _ _ k473 (XTop.xrun_seg_sound XCuts.z474 XCuts.b474 XCuts.z475 XCuts.b475 XCuts.n474 XCuts.v474 eq_refl XJ0474.seg).
Definition k475 := XR_trans _ _ _ _ _ _ _ _ _ _ k474 (XTop.xrun_seg_sound XCuts.z475 XCuts.b475 XCuts.z476 XCuts.b476 XCuts.n475 XCuts.v475 eq_refl XJ0475.seg).
Definition k476 := XR_trans _ _ _ _ _ _ _ _ _ _ k475 (XTop.xrun_seg_sound XCuts.z476 XCuts.b476 XCuts.z477 XCuts.b477 XCuts.n476 XCuts.v476 eq_refl XJ0476.seg).
Definition k477 := XR_trans _ _ _ _ _ _ _ _ _ _ k476 (XTop.xrun_seg_sound XCuts.z477 XCuts.b477 XCuts.z478 XCuts.b478 XCuts.n477 XCuts.v477 eq_refl XJ0477.seg).
Definition k478 := XR_trans _ _ _ _ _ _ _ _ _ _ k477 (XTop.xrun_seg_sound XCuts.z478 XCuts.b478 XCuts.z479 XCuts.b479 XCuts.n478 XCuts.v478 eq_refl XJ0478.seg).
Definition k479 := XR_trans _ _ _ _ _ _ _ _ _ _ k478 (XTop.xrun_seg_sound XCuts.z479 XCuts.b479 XCuts.z480 XCuts.b480 XCuts.n479 XCuts.v479 eq_refl XJ0479.seg).
Definition k480 := XR_trans _ _ _ _ _ _ _ _ _ _ k479 (XTop.xrun_seg_sound XCuts.z480 XCuts.b480 XCuts.z481 XCuts.b481 XCuts.n480 XCuts.v480 eq_refl XJ0480.seg).
Definition k481 := XR_trans _ _ _ _ _ _ _ _ _ _ k480 (XTop.xrun_seg_sound XCuts.z481 XCuts.b481 XCuts.z482 XCuts.b482 XCuts.n481 XCuts.v481 eq_refl XJ0481.seg).
Definition k482 := XR_trans _ _ _ _ _ _ _ _ _ _ k481 (XTop.xrun_seg_sound XCuts.z482 XCuts.b482 XCuts.z483 XCuts.b483 XCuts.n482 XCuts.v482 eq_refl XJ0482.seg).
Definition k483 := XR_trans _ _ _ _ _ _ _ _ _ _ k482 (XTop.xrun_seg_sound XCuts.z483 XCuts.b483 XCuts.z484 XCuts.b484 XCuts.n483 XCuts.v483 eq_refl XJ0483.seg).
Definition k484 := XR_trans _ _ _ _ _ _ _ _ _ _ k483 (XTop.xrun_seg_sound XCuts.z484 XCuts.b484 XCuts.z485 XCuts.b485 XCuts.n484 XCuts.v484 eq_refl XJ0484.seg).
Definition k485 := XR_trans _ _ _ _ _ _ _ _ _ _ k484 (XTop.xrun_seg_sound XCuts.z485 XCuts.b485 XCuts.z486 XCuts.b486 XCuts.n485 XCuts.v485 eq_refl XJ0485.seg).
Definition k486 := XR_trans _ _ _ _ _ _ _ _ _ _ k485 (XTop.xrun_seg_sound XCuts.z486 XCuts.b486 XCuts.z487 XCuts.b487 XCuts.n486 XCuts.v486 eq_refl XJ0486.seg).
Definition k487 := XR_trans _ _ _ _ _ _ _ _ _ _ k486 (XTop.xrun_seg_sound XCuts.z487 XCuts.b487 XCuts.z488 XCuts.b488 XCuts.n487 XCuts.v487 eq_refl XJ0487.seg).
Definition k488 := XR_trans _ _ _ _ _ _ _ _ _ _ k487 (XTop.xrun_seg_sound XCuts.z488 XCuts.b488 XCuts.z489 XCuts.b489 XCuts.n488 XCuts.v488 eq_refl XJ0488.seg).
Definition k489 := XR_trans _ _ _ _ _ _ _ _ _ _ k488 (XTop.xrun_seg_sound XCuts.z489 XCuts.b489 XCuts.z490 XCuts.b490 XCuts.n489 XCuts.v489 eq_refl XJ0489.seg).
Definition k490 := XR_trans _ _ _ _ _ _ _ _ _ _ k489 (XTop.xrun_seg_sound XCuts.z490 XCuts.b490 XCuts.z491 XCuts.b491 XCuts.n490 XCuts.v490 eq_refl XJ0490.seg).
Definition k491 := XR_trans _ _ _ _ _ _ _ _ _ _ k490 (XTop.xrun_seg_sound XCuts.z491 XCuts.b491 XCuts.z492 XCuts.b492 XCuts.n491 XCuts.v491 eq_refl XJ0491.seg).
Definition k492 := XR_trans _ _ _ _ _ _ _ _ _ _ k491 (XTop.xrun_seg_sound XCuts.z492 XCuts.b492 XCuts.z493 XCuts.b493 XCuts.n492 XCuts.v492 eq_refl XJ0492.seg).
Definition k493 := XR_trans _ _ _ _ _ _ _ _ _ _ k492 (XTop.xrun_seg_sound XCuts.z493 XCuts.b493 XCuts.z494 XCuts.b494 XCuts.n493 XCuts.v493 eq_refl XJ0493.seg).
Definition k494 := XR_trans _ _ _ _ _ _ _ _ _ _ k493 (XTop.xrun_seg_sound XCuts.z494 XCuts.b494 XCuts.z495 XCuts.b495 XCuts.n494 XCuts.v494 eq_refl XJ0494.seg).
Definition k495 := XR_trans _ _ _ _ _ _ _ _ _ _ k494 (XTop.xrun_seg_sound XCuts.z495 XCuts.b495 XCuts.z496 XCuts.b496 XCuts.n495 XCuts.v495 eq_refl XJ0495.seg).
Definition k496 := XR_trans _ _ _ _ _ _ _ _ _ _ k495 (XTop.xrun_seg_sound XCuts.z496 XCuts.b496 XCuts.z497 XCuts.b497 XCuts.n496 XCuts.v496 eq_refl XJ0496.seg).
Definition k497 := XR_trans _ _ _ _ _ _ _ _ _ _ k496 (XTop.xrun_seg_sound XCuts.z497 XCuts.b497 XCuts.z498 XCuts.b498 XCuts.n497 XCuts.v497 eq_refl XJ0497.seg).
Definition k498 := XR_trans _ _ _ _ _ _ _ _ _ _ k497 (XTop.xrun_seg_sound XCuts.z498 XCuts.b498 XCuts.z499 XCuts.b499 XCuts.n498 XCuts.v498 eq_refl XJ0498.seg).
Definition k499 := XR_trans _ _ _ _ _ _ _ _ _ _ k498 (XTop.xrun_seg_sound XCuts.z499 XCuts.b499 XCuts.z500 XCuts.b500 XCuts.n499 XCuts.v499 eq_refl XJ0499.seg).
Definition k500 := XR_trans _ _ _ _ _ _ _ _ _ _ k499 (XTop.xrun_seg_sound XCuts.z500 XCuts.b500 XCuts.z501 XCuts.b501 XCuts.n500 XCuts.v500 eq_refl XJ0500.seg).
Definition k501 := XR_trans _ _ _ _ _ _ _ _ _ _ k500 (XTop.xrun_seg_sound XCuts.z501 XCuts.b501 XCuts.z502 XCuts.b502 XCuts.n501 XCuts.v501 eq_refl XJ0501.seg).
Definition k502 := XR_trans _ _ _ _ _ _ _ _ _ _ k501 (XTop.xrun_seg_sound XCuts.z502 XCuts.b502 XCuts.z503 XCuts.b503 XCuts.n502 XCuts.v502 eq_refl XJ0502.seg).
Definition k503 := XR_trans _ _ _ _ _ _ _ _ _ _ k502 (XTop.xrun_seg_sound XCuts.z503 XCuts.b503 XCuts.z504 XCuts.b504 XCuts.n503 XCuts.v503 eq_refl XJ0503.seg).
Definition k504 := XR_trans _ _ _ _ _ _ _ _ _ _ k503 (XTop.xrun_seg_sound XCuts.z504 XCuts.b504 XCuts.z505 XCuts.b505 XCuts.n504 XCuts.v504 eq_refl XJ0504.seg).
Definition k505 := XR_trans _ _ _ _ _ _ _ _ _ _ k504 (XTop.xrun_seg_sound XCuts.z505 XCuts.b505 XCuts.z506 XCuts.b506 XCuts.n505 XCuts.v505 eq_refl XJ0505.seg).
Definition k506 := XR_trans _ _ _ _ _ _ _ _ _ _ k505 (XTop.xrun_seg_sound XCuts.z506 XCuts.b506 XCuts.z507 XCuts.b507 XCuts.n506 XCuts.v506 eq_refl XJ0506.seg).
Definition k507 := XR_trans _ _ _ _ _ _ _ _ _ _ k506 (XTop.xrun_seg_sound XCuts.z507 XCuts.b507 XCuts.z508 XCuts.b508 XCuts.n507 XCuts.v507 eq_refl XJ0507.seg).
Definition k508 := XR_trans _ _ _ _ _ _ _ _ _ _ k507 (XTop.xrun_seg_sound XCuts.z508 XCuts.b508 XCuts.z509 XCuts.b509 XCuts.n508 XCuts.v508 eq_refl XJ0508.seg).
Definition k509 := XR_trans _ _ _ _ _ _ _ _ _ _ k508 (XTop.xrun_seg_sound XCuts.z509 XCuts.b509 XCuts.z510 XCuts.b510 XCuts.n509 XCuts.v509 eq_refl XJ0509.seg).
Definition k510 := XR_trans _ _ _ _ _ _ _ _ _ _ k509 (XTop.xrun_seg_sound XCuts.z510 XCuts.b510 XCuts.z511 XCuts.b511 XCuts.n510 XCuts.v510 eq_refl XJ0510.seg).
Definition k511 := XR_trans _ _ _ _ _ _ _ _ _ _ k510 (XTop.xrun_seg_sound XCuts.z511 XCuts.b511 XCuts.z512 XCuts.b512 XCuts.n511 XCuts.v511 eq_refl XJ0511.seg).
Definition k512 := XR_trans _ _ _ _ _ _ _ _ _ _ k511 (XTop.xrun_seg_sound XCuts.z512 XCuts.b512 XCuts.z513 XCuts.b513 XCuts.n512 XCuts.v512 eq_refl XJ0512.seg).
Definition k513 := XR_trans _ _ _ _ _ _ _ _ _ _ k512 (XTop.xrun_seg_sound XCuts.z513 XCuts.b513 XCuts.z514 XCuts.b514 XCuts.n513 XCuts.v513 eq_refl XJ0513.seg).
Definition k514 := XR_trans _ _ _ _ _ _ _ _ _ _ k513 (XTop.xrun_seg_sound XCuts.z514 XCuts.b514 XCuts.z515 XCuts.b515 XCuts.n514 XCuts.v514 eq_refl XJ0514.seg).
Definition k515 := XR_trans _ _ _ _ _ _ _ _ _ _ k514 (XTop.xrun_seg_sound XCuts.z515 XCuts.b515 XCuts.z516 XCuts.b516 XCuts.n515 XCuts.v515 eq_refl XJ0515.seg).
Definition k516 := XR_trans _ _ _ _ _ _ _ _ _ _ k515 (XTop.xrun_seg_sound XCuts.z516 XCuts.b516 XCuts.z517 XCuts.b517 XCuts.n516 XCuts.v516 eq_refl XJ0516.seg).
Definition k517 := XR_trans _ _ _ _ _ _ _ _ _ _ k516 (XTop.xrun_seg_sound XCuts.z517 XCuts.b517 XCuts.z518 XCuts.b518 XCuts.n517 XCuts.v517 eq_refl XJ0517.seg).
Definition k518 := XR_trans _ _ _ _ _ _ _ _ _ _ k517 (XTop.xrun_seg_sound XCuts.z518 XCuts.b518 XCuts.z519 XCuts.b519 XCuts.n518 XCuts.v518 eq_refl XJ0518.seg).
Definition k519 := XR_trans _ _ _ _ _ _ _ _ _ _ k518 (XTop.xrun_seg_sound XCuts.z519 XCuts.b519 XCuts.z520 XCuts.b520 XCuts.n519 XCuts.v519 eq_refl XJ0519.seg).
Definition k520 := XR_trans _ _ _ _ _ _ _ _ _ _ k519 (XTop.xrun_seg_sound XCuts.z520 XCuts.b520 XCuts.z521 XCuts.b521 XCuts.n520 XCuts.v520 eq_refl XJ0520.seg).
Definition k521 := XR_trans _ _ _ _ _ _ _ _ _ _ k520 (XTop.xrun_seg_sound XCuts.z521 XCuts.b521 XCuts.z522 XCuts.b522 XCuts.n521 XCuts.v521 eq_refl XJ0521.seg).
Definition k522 := XR_trans _ _ _ _ _ _ _ _ _ _ k521 (XTop.xrun_seg_sound XCuts.z522 XCuts.b522 XCuts.z523 XCuts.b523 XCuts.n522 XCuts.v522 eq_refl XJ0522.seg).
Definition k523 := XR_trans _ _ _ _ _ _ _ _ _ _ k522 (XTop.xrun_seg_sound XCuts.z523 XCuts.b523 XCuts.z524 XCuts.b524 XCuts.n523 XCuts.v523 eq_refl XJ0523.seg).
Definition k524 := XR_trans _ _ _ _ _ _ _ _ _ _ k523 (XTop.xrun_seg_sound XCuts.z524 XCuts.b524 XCuts.z525 XCuts.b525 XCuts.n524 XCuts.v524 eq_refl XJ0524.seg).
Definition k525 := XR_trans _ _ _ _ _ _ _ _ _ _ k524 (XTop.xrun_seg_sound XCuts.z525 XCuts.b525 XCuts.z526 XCuts.b526 XCuts.n525 XCuts.v525 eq_refl XJ0525.seg).
Definition k526 := XR_trans _ _ _ _ _ _ _ _ _ _ k525 (XTop.xrun_seg_sound XCuts.z526 XCuts.b526 XCuts.z527 XCuts.b527 XCuts.n526 XCuts.v526 eq_refl XJ0526.seg).
Definition k527 := XR_trans _ _ _ _ _ _ _ _ _ _ k526 (XTop.xrun_seg_sound XCuts.z527 XCuts.b527 XCuts.z528 XCuts.b528 XCuts.n527 XCuts.v527 eq_refl XJ0527.seg).
Definition k528 := XR_trans _ _ _ _ _ _ _ _ _ _ k527 (XTop.xrun_seg_sound XCuts.z528 XCuts.b528 XCuts.z529 XCuts.b529 XCuts.n528 XCuts.v528 eq_refl XJ0528.seg).
Definition k529 := XR_trans _ _ _ _ _ _ _ _ _ _ k528 (XTop.xrun_seg_sound XCuts.z529 XCuts.b529 XCuts.z530 XCuts.b530 XCuts.n529 XCuts.v529 eq_refl XJ0529.seg).
Definition k530 := XR_trans _ _ _ _ _ _ _ _ _ _ k529 (XTop.xrun_seg_sound XCuts.z530 XCuts.b530 XCuts.z531 XCuts.b531 XCuts.n530 XCuts.v530 eq_refl XJ0530.seg).
Definition k531 := XR_trans _ _ _ _ _ _ _ _ _ _ k530 (XTop.xrun_seg_sound XCuts.z531 XCuts.b531 XCuts.z532 XCuts.b532 XCuts.n531 XCuts.v531 eq_refl XJ0531.seg).
Definition k532 := XR_trans _ _ _ _ _ _ _ _ _ _ k531 (XTop.xrun_seg_sound XCuts.z532 XCuts.b532 XCuts.z533 XCuts.b533 XCuts.n532 XCuts.v532 eq_refl XJ0532.seg).
Definition k533 := XR_trans _ _ _ _ _ _ _ _ _ _ k532 (XTop.xrun_seg_sound XCuts.z533 XCuts.b533 XCuts.z534 XCuts.b534 XCuts.n533 XCuts.v533 eq_refl XJ0533.seg).
Definition k534 := XR_trans _ _ _ _ _ _ _ _ _ _ k533 (XTop.xrun_seg_sound XCuts.z534 XCuts.b534 XCuts.z535 XCuts.b535 XCuts.n534 XCuts.v534 eq_refl XJ0534.seg).
Definition k535 := XR_trans _ _ _ _ _ _ _ _ _ _ k534 (XTop.xrun_seg_sound XCuts.z535 XCuts.b535 XCuts.z536 XCuts.b536 XCuts.n535 XCuts.v535 eq_refl XJ0535.seg).
Definition k536 := XR_trans _ _ _ _ _ _ _ _ _ _ k535 (XTop.xrun_seg_sound XCuts.z536 XCuts.b536 XCuts.z537 XCuts.b537 XCuts.n536 XCuts.v536 eq_refl XJ0536.seg).
Definition k537 := XR_trans _ _ _ _ _ _ _ _ _ _ k536 (XTop.xrun_seg_sound XCuts.z537 XCuts.b537 XCuts.z538 XCuts.b538 XCuts.n537 XCuts.v537 eq_refl XJ0537.seg).
Definition k538 := XR_trans _ _ _ _ _ _ _ _ _ _ k537 (XTop.xrun_seg_sound XCuts.z538 XCuts.b538 XCuts.z539 XCuts.b539 XCuts.n538 XCuts.v538 eq_refl XJ0538.seg).
Definition k539 := XR_trans _ _ _ _ _ _ _ _ _ _ k538 (XTop.xrun_seg_sound XCuts.z539 XCuts.b539 XCuts.z540 XCuts.b540 XCuts.n539 XCuts.v539 eq_refl XJ0539.seg).
Definition k540 := XR_trans _ _ _ _ _ _ _ _ _ _ k539 (XTop.xrun_seg_sound XCuts.z540 XCuts.b540 XCuts.z541 XCuts.b541 XCuts.n540 XCuts.v540 eq_refl XJ0540.seg).
Definition k541 := XR_trans _ _ _ _ _ _ _ _ _ _ k540 (XTop.xrun_seg_sound XCuts.z541 XCuts.b541 XCuts.z542 XCuts.b542 XCuts.n541 XCuts.v541 eq_refl XJ0541.seg).
Definition k542 := XR_trans _ _ _ _ _ _ _ _ _ _ k541 (XTop.xrun_seg_sound XCuts.z542 XCuts.b542 XCuts.z543 XCuts.b543 XCuts.n542 XCuts.v542 eq_refl XJ0542.seg).
Definition k543 := XR_trans _ _ _ _ _ _ _ _ _ _ k542 (XTop.xrun_seg_sound XCuts.z543 XCuts.b543 XCuts.z544 XCuts.b544 XCuts.n543 XCuts.v543 eq_refl XJ0543.seg).
Definition k544 := XR_trans _ _ _ _ _ _ _ _ _ _ k543 (XTop.xrun_seg_sound XCuts.z544 XCuts.b544 XCuts.z545 XCuts.b545 XCuts.n544 XCuts.v544 eq_refl XJ0544.seg).
Definition k545 := XR_trans _ _ _ _ _ _ _ _ _ _ k544 (XTop.xrun_seg_sound XCuts.z545 XCuts.b545 XCuts.z546 XCuts.b546 XCuts.n545 XCuts.v545 eq_refl XJ0545.seg).
Definition k546 := XR_trans _ _ _ _ _ _ _ _ _ _ k545 (XTop.xrun_seg_sound XCuts.z546 XCuts.b546 XCuts.z547 XCuts.b547 XCuts.n546 XCuts.v546 eq_refl XJ0546.seg).
Definition k547 := XR_trans _ _ _ _ _ _ _ _ _ _ k546 (XTop.xrun_seg_sound XCuts.z547 XCuts.b547 XCuts.z548 XCuts.b548 XCuts.n547 XCuts.v547 eq_refl XJ0547.seg).
Definition k548 := XR_trans _ _ _ _ _ _ _ _ _ _ k547 (XTop.xrun_seg_sound XCuts.z548 XCuts.b548 XCuts.z549 XCuts.b549 XCuts.n548 XCuts.v548 eq_refl XJ0548.seg).
Definition k549 := XR_trans _ _ _ _ _ _ _ _ _ _ k548 (XTop.xrun_seg_sound XCuts.z549 XCuts.b549 XCuts.z550 XCuts.b550 XCuts.n549 XCuts.v549 eq_refl XJ0549.seg).
Definition k550 := XR_trans _ _ _ _ _ _ _ _ _ _ k549 (XTop.xrun_seg_sound XCuts.z550 XCuts.b550 XCuts.z551 XCuts.b551 XCuts.n550 XCuts.v550 eq_refl XJ0550.seg).
Definition k551 := XR_trans _ _ _ _ _ _ _ _ _ _ k550 (XTop.xrun_seg_sound XCuts.z551 XCuts.b551 XCuts.z552 XCuts.b552 XCuts.n551 XCuts.v551 eq_refl XJ0551.seg).
Definition k552 := XR_trans _ _ _ _ _ _ _ _ _ _ k551 (XTop.xrun_seg_sound XCuts.z552 XCuts.b552 XCuts.z553 XCuts.b553 XCuts.n552 XCuts.v552 eq_refl XJ0552.seg).
Definition k553 := XR_trans _ _ _ _ _ _ _ _ _ _ k552 (XTop.xrun_seg_sound XCuts.z553 XCuts.b553 XCuts.z554 XCuts.b554 XCuts.n553 XCuts.v553 eq_refl XJ0553.seg).
Definition k554 := XR_trans _ _ _ _ _ _ _ _ _ _ k553 (XTop.xrun_seg_sound XCuts.z554 XCuts.b554 XCuts.z555 XCuts.b555 XCuts.n554 XCuts.v554 eq_refl XJ0554.seg).
Definition k555 := XR_trans _ _ _ _ _ _ _ _ _ _ k554 (XTop.xrun_seg_sound XCuts.z555 XCuts.b555 XCuts.z556 XCuts.b556 XCuts.n555 XCuts.v555 eq_refl XJ0555.seg).
Definition k556 := XR_trans _ _ _ _ _ _ _ _ _ _ k555 (XTop.xrun_seg_sound XCuts.z556 XCuts.b556 XCuts.z557 XCuts.b557 XCuts.n556 XCuts.v556 eq_refl XJ0556.seg).
Definition k557 := XR_trans _ _ _ _ _ _ _ _ _ _ k556 (XTop.xrun_seg_sound XCuts.z557 XCuts.b557 XCuts.z558 XCuts.b558 XCuts.n557 XCuts.v557 eq_refl XJ0557.seg).
Definition k558 := XR_trans _ _ _ _ _ _ _ _ _ _ k557 (XTop.xrun_seg_sound XCuts.z558 XCuts.b558 XCuts.z559 XCuts.b559 XCuts.n558 XCuts.v558 eq_refl XJ0558.seg).
Definition k559 := XR_trans _ _ _ _ _ _ _ _ _ _ k558 (XTop.xrun_seg_sound XCuts.z559 XCuts.b559 XCuts.z560 XCuts.b560 XCuts.n559 XCuts.v559 eq_refl XJ0559.seg).
Definition k560 := XR_trans _ _ _ _ _ _ _ _ _ _ k559 (XTop.xrun_seg_sound XCuts.z560 XCuts.b560 XCuts.z561 XCuts.b561 XCuts.n560 XCuts.v560 eq_refl XJ0560.seg).
Definition k561 := XR_trans _ _ _ _ _ _ _ _ _ _ k560 (XTop.xrun_seg_sound XCuts.z561 XCuts.b561 XCuts.z562 XCuts.b562 XCuts.n561 XCuts.v561 eq_refl XJ0561.seg).
Definition k562 := XR_trans _ _ _ _ _ _ _ _ _ _ k561 (XTop.xrun_seg_sound XCuts.z562 XCuts.b562 XCuts.z563 XCuts.b563 XCuts.n562 XCuts.v562 eq_refl XJ0562.seg).
Definition k563 := XR_trans _ _ _ _ _ _ _ _ _ _ k562 (XTop.xrun_seg_sound XCuts.z563 XCuts.b563 XCuts.z564 XCuts.b564 XCuts.n563 XCuts.v563 eq_refl XJ0563.seg).
Definition k564 := XR_trans _ _ _ _ _ _ _ _ _ _ k563 (XTop.xrun_seg_sound XCuts.z564 XCuts.b564 XCuts.z565 XCuts.b565 XCuts.n564 XCuts.v564 eq_refl XJ0564.seg).
Definition k565 := XR_trans _ _ _ _ _ _ _ _ _ _ k564 (XTop.xrun_seg_sound XCuts.z565 XCuts.b565 XCuts.z566 XCuts.b566 XCuts.n565 XCuts.v565 eq_refl XJ0565.seg).
Definition k566 := XR_trans _ _ _ _ _ _ _ _ _ _ k565 (XTop.xrun_seg_sound XCuts.z566 XCuts.b566 XCuts.z567 XCuts.b567 XCuts.n566 XCuts.v566 eq_refl XJ0566.seg).
Definition k567 := XR_trans _ _ _ _ _ _ _ _ _ _ k566 (XTop.xrun_seg_sound XCuts.z567 XCuts.b567 XCuts.z568 XCuts.b568 XCuts.n567 XCuts.v567 eq_refl XJ0567.seg).
Definition k568 := XR_trans _ _ _ _ _ _ _ _ _ _ k567 (XTop.xrun_seg_sound XCuts.z568 XCuts.b568 XCuts.z569 XCuts.b569 XCuts.n568 XCuts.v568 eq_refl XJ0568.seg).
Definition k569 := XR_trans _ _ _ _ _ _ _ _ _ _ k568 (XTop.xrun_seg_sound XCuts.z569 XCuts.b569 XCuts.z570 XCuts.b570 XCuts.n569 XCuts.v569 eq_refl XJ0569.seg).
Definition k570 := XR_trans _ _ _ _ _ _ _ _ _ _ k569 (XTop.xrun_seg_sound XCuts.z570 XCuts.b570 XCuts.z571 XCuts.b571 XCuts.n570 XCuts.v570 eq_refl XJ0570.seg).
Definition k571 := XR_trans _ _ _ _ _ _ _ _ _ _ k570 (XTop.xrun_seg_sound XCuts.z571 XCuts.b571 XCuts.z572 XCuts.b572 XCuts.n571 XCuts.v571 eq_refl XJ0571.seg).
Definition k572 := XR_trans _ _ _ _ _ _ _ _ _ _ k571 (XTop.xrun_seg_sound XCuts.z572 XCuts.b572 XCuts.z573 XCuts.b573 XCuts.n572 XCuts.v572 eq_refl XJ0572.seg).
Definition k573 := XR_trans _ _ _ _ _ _ _ _ _ _ k572 (XTop.xrun_seg_sound XCuts.z573 XCuts.b573 XCuts.z574 XCuts.b574 XCuts.n573 XCuts.v573 eq_refl XJ0573.seg).
Definition k574 := XR_trans _ _ _ _ _ _ _ _ _ _ k573 (XTop.xrun_seg_sound XCuts.z574 XCuts.b574 XCuts.z575 XCuts.b575 XCuts.n574 XCuts.v574 eq_refl XJ0574.seg).
Definition k575 := XR_trans _ _ _ _ _ _ _ _ _ _ k574 (XTop.xrun_seg_sound XCuts.z575 XCuts.b575 XCuts.z576 XCuts.b576 XCuts.n575 XCuts.v575 eq_refl XJ0575.seg).
Definition k576 := XR_trans _ _ _ _ _ _ _ _ _ _ k575 (XTop.xrun_seg_sound XCuts.z576 XCuts.b576 XCuts.z577 XCuts.b577 XCuts.n576 XCuts.v576 eq_refl XJ0576.seg).
Definition k577 := XR_trans _ _ _ _ _ _ _ _ _ _ k576 (XTop.xrun_seg_sound XCuts.z577 XCuts.b577 XCuts.z578 XCuts.b578 XCuts.n577 XCuts.v577 eq_refl XJ0577.seg).
Definition k578 := XR_trans _ _ _ _ _ _ _ _ _ _ k577 (XTop.xrun_seg_sound XCuts.z578 XCuts.b578 XCuts.z579 XCuts.b579 XCuts.n578 XCuts.v578 eq_refl XJ0578.seg).
Definition k579 := XR_trans _ _ _ _ _ _ _ _ _ _ k578 (XTop.xrun_seg_sound XCuts.z579 XCuts.b579 XCuts.z580 XCuts.b580 XCuts.n579 XCuts.v579 eq_refl XJ0579.seg).
Definition k580 := XR_trans _ _ _ _ _ _ _ _ _ _ k579 (XTop.xrun_seg_sound XCuts.z580 XCuts.b580 XCuts.z581 XCuts.b581 XCuts.n580 XCuts.v580 eq_refl XJ0580.seg).
Definition k581 := XR_trans _ _ _ _ _ _ _ _ _ _ k580 (XTop.xrun_seg_sound XCuts.z581 XCuts.b581 XCuts.z582 XCuts.b582 XCuts.n581 XCuts.v581 eq_refl XJ0581.seg).
Definition k582 := XR_trans _ _ _ _ _ _ _ _ _ _ k581 (XTop.xrun_seg_sound XCuts.z582 XCuts.b582 XCuts.z583 XCuts.b583 XCuts.n582 XCuts.v582 eq_refl XJ0582.seg).
Definition k583 := XR_trans _ _ _ _ _ _ _ _ _ _ k582 (XTop.xrun_seg_sound XCuts.z583 XCuts.b583 XCuts.z584 XCuts.b584 XCuts.n583 XCuts.v583 eq_refl XJ0583.seg).
Definition k584 := XR_trans _ _ _ _ _ _ _ _ _ _ k583 (XTop.xrun_seg_sound XCuts.z584 XCuts.b584 XCuts.z585 XCuts.b585 XCuts.n584 XCuts.v584 eq_refl XJ0584.seg).
Definition k585 := XR_trans _ _ _ _ _ _ _ _ _ _ k584 (XTop.xrun_seg_sound XCuts.z585 XCuts.b585 XCuts.z586 XCuts.b586 XCuts.n585 XCuts.v585 eq_refl XJ0585.seg).
Definition k586 := XR_trans _ _ _ _ _ _ _ _ _ _ k585 (XTop.xrun_seg_sound XCuts.z586 XCuts.b586 XCuts.z587 XCuts.b587 XCuts.n586 XCuts.v586 eq_refl XJ0586.seg).
Definition k587 := XR_trans _ _ _ _ _ _ _ _ _ _ k586 (XTop.xrun_seg_sound XCuts.z587 XCuts.b587 XCuts.z588 XCuts.b588 XCuts.n587 XCuts.v587 eq_refl XJ0587.seg).
Definition k588 := XR_trans _ _ _ _ _ _ _ _ _ _ k587 (XTop.xrun_seg_sound XCuts.z588 XCuts.b588 XCuts.z589 XCuts.b589 XCuts.n588 XCuts.v588 eq_refl XJ0588.seg).
Definition k589 := XR_trans _ _ _ _ _ _ _ _ _ _ k588 (XTop.xrun_seg_sound XCuts.z589 XCuts.b589 XCuts.z590 XCuts.b590 XCuts.n589 XCuts.v589 eq_refl XJ0589.seg).
Definition k590 := XR_trans _ _ _ _ _ _ _ _ _ _ k589 (XTop.xrun_seg_sound XCuts.z590 XCuts.b590 XCuts.z591 XCuts.b591 XCuts.n590 XCuts.v590 eq_refl XJ0590.seg).
Definition k591 := XR_trans _ _ _ _ _ _ _ _ _ _ k590 (XTop.xrun_seg_sound XCuts.z591 XCuts.b591 XCuts.z592 XCuts.b592 XCuts.n591 XCuts.v591 eq_refl XJ0591.seg).
Definition k592 := XR_trans _ _ _ _ _ _ _ _ _ _ k591 (XTop.xrun_seg_sound XCuts.z592 XCuts.b592 XCuts.z593 XCuts.b593 XCuts.n592 XCuts.v592 eq_refl XJ0592.seg).
Definition k593 := XR_trans _ _ _ _ _ _ _ _ _ _ k592 (XTop.xrun_seg_sound XCuts.z593 XCuts.b593 XCuts.z594 XCuts.b594 XCuts.n593 XCuts.v593 eq_refl XJ0593.seg).
Definition k594 := XR_trans _ _ _ _ _ _ _ _ _ _ k593 (XTop.xrun_seg_sound XCuts.z594 XCuts.b594 XCuts.z595 XCuts.b595 XCuts.n594 XCuts.v594 eq_refl XJ0594.seg).
Definition k595 := XR_trans _ _ _ _ _ _ _ _ _ _ k594 (XTop.xrun_seg_sound XCuts.z595 XCuts.b595 XCuts.z596 XCuts.b596 XCuts.n595 XCuts.v595 eq_refl XJ0595.seg).
Definition k596 := XR_trans _ _ _ _ _ _ _ _ _ _ k595 (XTop.xrun_seg_sound XCuts.z596 XCuts.b596 XCuts.z597 XCuts.b597 XCuts.n596 XCuts.v596 eq_refl XJ0596.seg).
Definition k597 := XR_trans _ _ _ _ _ _ _ _ _ _ k596 (XTop.xrun_seg_sound XCuts.z597 XCuts.b597 XCuts.z598 XCuts.b598 XCuts.n597 XCuts.v597 eq_refl XJ0597.seg).
Definition k598 := XR_trans _ _ _ _ _ _ _ _ _ _ k597 (XTop.xrun_seg_sound XCuts.z598 XCuts.b598 XCuts.z599 XCuts.b599 XCuts.n598 XCuts.v598 eq_refl XJ0598.seg).
Definition k599 := XR_trans _ _ _ _ _ _ _ _ _ _ k598 (XTop.xrun_seg_sound XCuts.z599 XCuts.b599 XCuts.z600 XCuts.b600 XCuts.n599 XCuts.v599 eq_refl XJ0599.seg).
Definition k600 := XR_trans _ _ _ _ _ _ _ _ _ _ k599 (XTop.xrun_seg_sound XCuts.z600 XCuts.b600 XCuts.z601 XCuts.b601 XCuts.n600 XCuts.v600 eq_refl XJ0600.seg).
Definition k601 := XR_trans _ _ _ _ _ _ _ _ _ _ k600 (XTop.xrun_seg_sound XCuts.z601 XCuts.b601 XCuts.z602 XCuts.b602 XCuts.n601 XCuts.v601 eq_refl XJ0601.seg).
Definition k602 := XR_trans _ _ _ _ _ _ _ _ _ _ k601 (XTop.xrun_seg_sound XCuts.z602 XCuts.b602 XCuts.z603 XCuts.b603 XCuts.n602 XCuts.v602 eq_refl XJ0602.seg).
Definition k603 := XR_trans _ _ _ _ _ _ _ _ _ _ k602 (XTop.xrun_seg_sound XCuts.z603 XCuts.b603 XCuts.z604 XCuts.b604 XCuts.n603 XCuts.v603 eq_refl XJ0603.seg).
Definition k604 := XR_trans _ _ _ _ _ _ _ _ _ _ k603 (XTop.xrun_seg_sound XCuts.z604 XCuts.b604 XCuts.z605 XCuts.b605 XCuts.n604 XCuts.v604 eq_refl XJ0604.seg).
Definition k605 := XR_trans _ _ _ _ _ _ _ _ _ _ k604 (XTop.xrun_seg_sound XCuts.z605 XCuts.b605 XCuts.z606 XCuts.b606 XCuts.n605 XCuts.v605 eq_refl XJ0605.seg).
Definition k606 := XR_trans _ _ _ _ _ _ _ _ _ _ k605 (XTop.xrun_seg_sound XCuts.z606 XCuts.b606 XCuts.z607 XCuts.b607 XCuts.n606 XCuts.v606 eq_refl XJ0606.seg).
Definition k607 := XR_trans _ _ _ _ _ _ _ _ _ _ k606 (XTop.xrun_seg_sound XCuts.z607 XCuts.b607 XCuts.z608 XCuts.b608 XCuts.n607 XCuts.v607 eq_refl XJ0607.seg).
Definition k608 := XR_trans _ _ _ _ _ _ _ _ _ _ k607 (XTop.xrun_seg_sound XCuts.z608 XCuts.b608 XCuts.z609 XCuts.b609 XCuts.n608 XCuts.v608 eq_refl XJ0608.seg).
Definition k609 := XR_trans _ _ _ _ _ _ _ _ _ _ k608 (XTop.xrun_seg_sound XCuts.z609 XCuts.b609 XCuts.z610 XCuts.b610 XCuts.n609 XCuts.v609 eq_refl XJ0609.seg).
Definition k610 := XR_trans _ _ _ _ _ _ _ _ _ _ k609 (XTop.xrun_seg_sound XCuts.z610 XCuts.b610 XCuts.z611 XCuts.b611 XCuts.n610 XCuts.v610 eq_refl XJ0610.seg).
Definition k611 := XR_trans _ _ _ _ _ _ _ _ _ _ k610 (XTop.xrun_seg_sound XCuts.z611 XCuts.b611 XCuts.z612 XCuts.b612 XCuts.n611 XCuts.v611 eq_refl XJ0611.seg).
Definition k612 := XR_trans _ _ _ _ _ _ _ _ _ _ k611 (XTop.xrun_seg_sound XCuts.z612 XCuts.b612 XCuts.z613 XCuts.b613 XCuts.n612 XCuts.v612 eq_refl XJ0612.seg).
Definition k613 := XR_trans _ _ _ _ _ _ _ _ _ _ k612 (XTop.xrun_seg_sound XCuts.z613 XCuts.b613 XCuts.z614 XCuts.b614 XCuts.n613 XCuts.v613 eq_refl XJ0613.seg).
Definition k614 := XR_trans _ _ _ _ _ _ _ _ _ _ k613 (XTop.xrun_seg_sound XCuts.z614 XCuts.b614 XCuts.z615 XCuts.b615 XCuts.n614 XCuts.v614 eq_refl XJ0614.seg).
Definition k615 := XR_trans _ _ _ _ _ _ _ _ _ _ k614 (XTop.xrun_seg_sound XCuts.z615 XCuts.b615 XCuts.z616 XCuts.b616 XCuts.n615 XCuts.v615 eq_refl XJ0615.seg).
Definition k616 := XR_trans _ _ _ _ _ _ _ _ _ _ k615 (XTop.xrun_seg_sound XCuts.z616 XCuts.b616 XCuts.z617 XCuts.b617 XCuts.n616 XCuts.v616 eq_refl XJ0616.seg).
Definition k617 := XR_trans _ _ _ _ _ _ _ _ _ _ k616 (XTop.xrun_seg_sound XCuts.z617 XCuts.b617 XCuts.z618 XCuts.b618 XCuts.n617 XCuts.v617 eq_refl XJ0617.seg).
Definition k618 := XR_trans _ _ _ _ _ _ _ _ _ _ k617 (XTop.xrun_seg_sound XCuts.z618 XCuts.b618 XCuts.z619 XCuts.b619 XCuts.n618 XCuts.v618 eq_refl XJ0618.seg).
Definition k619 := XR_trans _ _ _ _ _ _ _ _ _ _ k618 (XTop.xrun_seg_sound XCuts.z619 XCuts.b619 XCuts.z620 XCuts.b620 XCuts.n619 XCuts.v619 eq_refl XJ0619.seg).
Definition k620 := XR_trans _ _ _ _ _ _ _ _ _ _ k619 (XTop.xrun_seg_sound XCuts.z620 XCuts.b620 XCuts.z621 XCuts.b621 XCuts.n620 XCuts.v620 eq_refl XJ0620.seg).
Definition k621 := XR_trans _ _ _ _ _ _ _ _ _ _ k620 (XTop.xrun_seg_sound XCuts.z621 XCuts.b621 XCuts.z622 XCuts.b622 XCuts.n621 XCuts.v621 eq_refl XJ0621.seg).
Definition k622 := XR_trans _ _ _ _ _ _ _ _ _ _ k621 (XTop.xrun_seg_sound XCuts.z622 XCuts.b622 XCuts.z623 XCuts.b623 XCuts.n622 XCuts.v622 eq_refl XJ0622.seg).
Definition k623 := XR_trans _ _ _ _ _ _ _ _ _ _ k622 (XTop.xrun_seg_sound XCuts.z623 XCuts.b623 XCuts.z624 XCuts.b624 XCuts.n623 XCuts.v623 eq_refl XJ0623.seg).
Definition k624 := XR_trans _ _ _ _ _ _ _ _ _ _ k623 (XTop.xrun_seg_sound XCuts.z624 XCuts.b624 XCuts.z625 XCuts.b625 XCuts.n624 XCuts.v624 eq_refl XJ0624.seg).
Definition k625 := XR_trans _ _ _ _ _ _ _ _ _ _ k624 (XTop.xrun_seg_sound XCuts.z625 XCuts.b625 XCuts.z626 XCuts.b626 XCuts.n625 XCuts.v625 eq_refl XJ0625.seg).
Definition k626 := XR_trans _ _ _ _ _ _ _ _ _ _ k625 (XTop.xrun_seg_sound XCuts.z626 XCuts.b626 XCuts.z627 XCuts.b627 XCuts.n626 XCuts.v626 eq_refl XJ0626.seg).
Definition k627 := XR_trans _ _ _ _ _ _ _ _ _ _ k626 (XTop.xrun_seg_sound XCuts.z627 XCuts.b627 XCuts.z628 XCuts.b628 XCuts.n627 XCuts.v627 eq_refl XJ0627.seg).
Definition k628 := XR_trans _ _ _ _ _ _ _ _ _ _ k627 (XTop.xrun_seg_sound XCuts.z628 XCuts.b628 XCuts.z629 XCuts.b629 XCuts.n628 XCuts.v628 eq_refl XJ0628.seg).
Definition k629 := XR_trans _ _ _ _ _ _ _ _ _ _ k628 (XTop.xrun_seg_sound XCuts.z629 XCuts.b629 XCuts.z630 XCuts.b630 XCuts.n629 XCuts.v629 eq_refl XJ0629.seg).
Definition k630 := XR_trans _ _ _ _ _ _ _ _ _ _ k629 (XTop.xrun_seg_sound XCuts.z630 XCuts.b630 XCuts.z631 XCuts.b631 XCuts.n630 XCuts.v630 eq_refl XJ0630.seg).
Definition k631 := XR_trans _ _ _ _ _ _ _ _ _ _ k630 (XTop.xrun_seg_sound XCuts.z631 XCuts.b631 XCuts.z632 XCuts.b632 XCuts.n631 XCuts.v631 eq_refl XJ0631.seg).
Definition k632 := XR_trans _ _ _ _ _ _ _ _ _ _ k631 (XTop.xrun_seg_sound XCuts.z632 XCuts.b632 XCuts.z633 XCuts.b633 XCuts.n632 XCuts.v632 eq_refl XJ0632.seg).
Definition k633 := XR_trans _ _ _ _ _ _ _ _ _ _ k632 (XTop.xrun_seg_sound XCuts.z633 XCuts.b633 XCuts.z634 XCuts.b634 XCuts.n633 XCuts.v633 eq_refl XJ0633.seg).
Definition k634 := XR_trans _ _ _ _ _ _ _ _ _ _ k633 (XTop.xrun_seg_sound XCuts.z634 XCuts.b634 XCuts.z635 XCuts.b635 XCuts.n634 XCuts.v634 eq_refl XJ0634.seg).
Definition k635 := XR_trans _ _ _ _ _ _ _ _ _ _ k634 (XTop.xrun_seg_sound XCuts.z635 XCuts.b635 XCuts.z636 XCuts.b636 XCuts.n635 XCuts.v635 eq_refl XJ0635.seg).
Definition k636 := XR_trans _ _ _ _ _ _ _ _ _ _ k635 (XTop.xrun_seg_sound XCuts.z636 XCuts.b636 XCuts.z637 XCuts.b637 XCuts.n636 XCuts.v636 eq_refl XJ0636.seg).
Definition k637 := XR_trans _ _ _ _ _ _ _ _ _ _ k636 (XTop.xrun_seg_sound XCuts.z637 XCuts.b637 XCuts.z638 XCuts.b638 XCuts.n637 XCuts.v637 eq_refl XJ0637.seg).
Definition k638 := XR_trans _ _ _ _ _ _ _ _ _ _ k637 (XTop.xrun_seg_sound XCuts.z638 XCuts.b638 XCuts.z639 XCuts.b639 XCuts.n638 XCuts.v638 eq_refl XJ0638.seg).
Definition k639 := XR_trans _ _ _ _ _ _ _ _ _ _ k638 (XTop.xrun_seg_sound XCuts.z639 XCuts.b639 XCuts.z640 XCuts.b640 XCuts.n639 XCuts.v639 eq_refl XJ0639.seg).
Definition k640 := XR_trans _ _ _ _ _ _ _ _ _ _ k639 (XTop.xrun_seg_sound XCuts.z640 XCuts.b640 XCuts.z641 XCuts.b641 XCuts.n640 XCuts.v640 eq_refl XJ0640.seg).
Definition k641 := XR_trans _ _ _ _ _ _ _ _ _ _ k640 (XTop.xrun_seg_sound XCuts.z641 XCuts.b641 XCuts.z642 XCuts.b642 XCuts.n641 XCuts.v641 eq_refl XJ0641.seg).
Definition k642 := XR_trans _ _ _ _ _ _ _ _ _ _ k641 (XTop.xrun_seg_sound XCuts.z642 XCuts.b642 XCuts.z643 XCuts.b643 XCuts.n642 XCuts.v642 eq_refl XJ0642.seg).
Definition k643 := XR_trans _ _ _ _ _ _ _ _ _ _ k642 (XTop.xrun_seg_sound XCuts.z643 XCuts.b643 XCuts.z644 XCuts.b644 XCuts.n643 XCuts.v643 eq_refl XJ0643.seg).
Definition k644 := XR_trans _ _ _ _ _ _ _ _ _ _ k643 (XTop.xrun_seg_sound XCuts.z644 XCuts.b644 XCuts.z645 XCuts.b645 XCuts.n644 XCuts.v644 eq_refl XJ0644.seg).
Definition k645 := XR_trans _ _ _ _ _ _ _ _ _ _ k644 (XTop.xrun_seg_sound XCuts.z645 XCuts.b645 XCuts.z646 XCuts.b646 XCuts.n645 XCuts.v645 eq_refl XJ0645.seg).
Definition k646 := XR_trans _ _ _ _ _ _ _ _ _ _ k645 (XTop.xrun_seg_sound XCuts.z646 XCuts.b646 XCuts.z647 XCuts.b647 XCuts.n646 XCuts.v646 eq_refl XJ0646.seg).
Definition k647 := XR_trans _ _ _ _ _ _ _ _ _ _ k646 (XTop.xrun_seg_sound XCuts.z647 XCuts.b647 XCuts.z648 XCuts.b648 XCuts.n647 XCuts.v647 eq_refl XJ0647.seg).
Definition k648 := XR_trans _ _ _ _ _ _ _ _ _ _ k647 (XTop.xrun_seg_sound XCuts.z648 XCuts.b648 XCuts.z649 XCuts.b649 XCuts.n648 XCuts.v648 eq_refl XJ0648.seg).
Definition k649 := XR_trans _ _ _ _ _ _ _ _ _ _ k648 (XTop.xrun_seg_sound XCuts.z649 XCuts.b649 XCuts.z650 XCuts.b650 XCuts.n649 XCuts.v649 eq_refl XJ0649.seg).
Definition k650 := XR_trans _ _ _ _ _ _ _ _ _ _ k649 (XTop.xrun_seg_sound XCuts.z650 XCuts.b650 XCuts.z651 XCuts.b651 XCuts.n650 XCuts.v650 eq_refl XJ0650.seg).
Definition k651 := XR_trans _ _ _ _ _ _ _ _ _ _ k650 (XTop.xrun_seg_sound XCuts.z651 XCuts.b651 XCuts.z652 XCuts.b652 XCuts.n651 XCuts.v651 eq_refl XJ0651.seg).
Definition k652 := XR_trans _ _ _ _ _ _ _ _ _ _ k651 (XTop.xrun_seg_sound XCuts.z652 XCuts.b652 XCuts.z653 XCuts.b653 XCuts.n652 XCuts.v652 eq_refl XJ0652.seg).
Definition k653 := XR_trans _ _ _ _ _ _ _ _ _ _ k652 (XTop.xrun_seg_sound XCuts.z653 XCuts.b653 XCuts.z654 XCuts.b654 XCuts.n653 XCuts.v653 eq_refl XJ0653.seg).
Definition k654 := XR_trans _ _ _ _ _ _ _ _ _ _ k653 (XTop.xrun_seg_sound XCuts.z654 XCuts.b654 XCuts.z655 XCuts.b655 XCuts.n654 XCuts.v654 eq_refl XJ0654.seg).
Definition k655 := XR_trans _ _ _ _ _ _ _ _ _ _ k654 (XTop.xrun_seg_sound XCuts.z655 XCuts.b655 XCuts.z656 XCuts.b656 XCuts.n655 XCuts.v655 eq_refl XJ0655.seg).
Definition k656 := XR_trans _ _ _ _ _ _ _ _ _ _ k655 (XTop.xrun_seg_sound XCuts.z656 XCuts.b656 XCuts.z657 XCuts.b657 XCuts.n656 XCuts.v656 eq_refl XJ0656.seg).
Definition k657 := XR_trans _ _ _ _ _ _ _ _ _ _ k656 (XTop.xrun_seg_sound XCuts.z657 XCuts.b657 XCuts.z658 XCuts.b658 XCuts.n657 XCuts.v657 eq_refl XJ0657.seg).
Definition k658 := XR_trans _ _ _ _ _ _ _ _ _ _ k657 (XTop.xrun_seg_sound XCuts.z658 XCuts.b658 XCuts.z659 XCuts.b659 XCuts.n658 XCuts.v658 eq_refl XJ0658.seg).
Definition k659 := XR_trans _ _ _ _ _ _ _ _ _ _ k658 (XTop.xrun_seg_sound XCuts.z659 XCuts.b659 XCuts.z660 XCuts.b660 XCuts.n659 XCuts.v659 eq_refl XJ0659.seg).
Definition k660 := XR_trans _ _ _ _ _ _ _ _ _ _ k659 (XTop.xrun_seg_sound XCuts.z660 XCuts.b660 XCuts.z661 XCuts.b661 XCuts.n660 XCuts.v660 eq_refl XJ0660.seg).
Definition k661 := XR_trans _ _ _ _ _ _ _ _ _ _ k660 (XTop.xrun_seg_sound XCuts.z661 XCuts.b661 XCuts.z662 XCuts.b662 XCuts.n661 XCuts.v661 eq_refl XJ0661.seg).
Definition k662 := XR_trans _ _ _ _ _ _ _ _ _ _ k661 (XTop.xrun_seg_sound XCuts.z662 XCuts.b662 XCuts.z663 XCuts.b663 XCuts.n662 XCuts.v662 eq_refl XJ0662.seg).
Definition k663 := XR_trans _ _ _ _ _ _ _ _ _ _ k662 (XTop.xrun_seg_sound XCuts.z663 XCuts.b663 XCuts.z664 XCuts.b664 XCuts.n663 XCuts.v663 eq_refl XJ0663.seg).
Definition k664 := XR_trans _ _ _ _ _ _ _ _ _ _ k663 (XTop.xrun_seg_sound XCuts.z664 XCuts.b664 XCuts.z665 XCuts.b665 XCuts.n664 XCuts.v664 eq_refl XJ0664.seg).
Definition k665 := XR_trans _ _ _ _ _ _ _ _ _ _ k664 (XTop.xrun_seg_sound XCuts.z665 XCuts.b665 XCuts.z666 XCuts.b666 XCuts.n665 XCuts.v665 eq_refl XJ0665.seg).
Definition k666 := XR_trans _ _ _ _ _ _ _ _ _ _ k665 (XTop.xrun_seg_sound XCuts.z666 XCuts.b666 XCuts.z667 XCuts.b667 XCuts.n666 XCuts.v666 eq_refl XJ0666.seg).
Definition k667 := XR_trans _ _ _ _ _ _ _ _ _ _ k666 (XTop.xrun_seg_sound XCuts.z667 XCuts.b667 XCuts.z668 XCuts.b668 XCuts.n667 XCuts.v667 eq_refl XJ0667.seg).
Definition k668 := XR_trans _ _ _ _ _ _ _ _ _ _ k667 (XTop.xrun_seg_sound XCuts.z668 XCuts.b668 XCuts.z669 XCuts.b669 XCuts.n668 XCuts.v668 eq_refl XJ0668.seg).
Definition k669 := XR_trans _ _ _ _ _ _ _ _ _ _ k668 (XTop.xrun_seg_sound XCuts.z669 XCuts.b669 XCuts.z670 XCuts.b670 XCuts.n669 XCuts.v669 eq_refl XJ0669.seg).
Definition k670 := XR_trans _ _ _ _ _ _ _ _ _ _ k669 (XTop.xrun_seg_sound XCuts.z670 XCuts.b670 XCuts.z671 XCuts.b671 XCuts.n670 XCuts.v670 eq_refl XJ0670.seg).
Definition k671 := XR_trans _ _ _ _ _ _ _ _ _ _ k670 (XTop.xrun_seg_sound XCuts.z671 XCuts.b671 XCuts.z672 XCuts.b672 XCuts.n671 XCuts.v671 eq_refl XJ0671.seg).
Definition k672 := XR_trans _ _ _ _ _ _ _ _ _ _ k671 (XTop.xrun_seg_sound XCuts.z672 XCuts.b672 XCuts.z673 XCuts.b673 XCuts.n672 XCuts.v672 eq_refl XJ0672.seg).
Definition k673 := XR_trans _ _ _ _ _ _ _ _ _ _ k672 (XTop.xrun_seg_sound XCuts.z673 XCuts.b673 XCuts.z674 XCuts.b674 XCuts.n673 XCuts.v673 eq_refl XJ0673.seg).
Definition k674 := XR_trans _ _ _ _ _ _ _ _ _ _ k673 (XTop.xrun_seg_sound XCuts.z674 XCuts.b674 XCuts.z675 XCuts.b675 XCuts.n674 XCuts.v674 eq_refl XJ0674.seg).
Definition k675 := XR_trans _ _ _ _ _ _ _ _ _ _ k674 (XTop.xrun_seg_sound XCuts.z675 XCuts.b675 XCuts.z676 XCuts.b676 XCuts.n675 XCuts.v675 eq_refl XJ0675.seg).
Definition k676 := XR_trans _ _ _ _ _ _ _ _ _ _ k675 (XTop.xrun_seg_sound XCuts.z676 XCuts.b676 XCuts.z677 XCuts.b677 XCuts.n676 XCuts.v676 eq_refl XJ0676.seg).
Definition k677 := XR_trans _ _ _ _ _ _ _ _ _ _ k676 (XTop.xrun_seg_sound XCuts.z677 XCuts.b677 XCuts.z678 XCuts.b678 XCuts.n677 XCuts.v677 eq_refl XJ0677.seg).
Definition k678 := XR_trans _ _ _ _ _ _ _ _ _ _ k677 (XTop.xrun_seg_sound XCuts.z678 XCuts.b678 XCuts.z679 XCuts.b679 XCuts.n678 XCuts.v678 eq_refl XJ0678.seg).
Definition k679 := XR_trans _ _ _ _ _ _ _ _ _ _ k678 (XTop.xrun_seg_sound XCuts.z679 XCuts.b679 XCuts.z680 XCuts.b680 XCuts.n679 XCuts.v679 eq_refl XJ0679.seg).
Definition k680 := XR_trans _ _ _ _ _ _ _ _ _ _ k679 (XTop.xrun_seg_sound XCuts.z680 XCuts.b680 XCuts.z681 XCuts.b681 XCuts.n680 XCuts.v680 eq_refl XJ0680.seg).
Definition k681 := XR_trans _ _ _ _ _ _ _ _ _ _ k680 (XTop.xrun_seg_sound XCuts.z681 XCuts.b681 XCuts.z682 XCuts.b682 XCuts.n681 XCuts.v681 eq_refl XJ0681.seg).
Definition k682 := XR_trans _ _ _ _ _ _ _ _ _ _ k681 (XTop.xrun_seg_sound XCuts.z682 XCuts.b682 XCuts.z683 XCuts.b683 XCuts.n682 XCuts.v682 eq_refl XJ0682.seg).
Definition k683 := XR_trans _ _ _ _ _ _ _ _ _ _ k682 (XTop.xrun_seg_sound XCuts.z683 XCuts.b683 XCuts.z684 XCuts.b684 XCuts.n683 XCuts.v683 eq_refl XJ0683.seg).
Definition k684 := XR_trans _ _ _ _ _ _ _ _ _ _ k683 (XTop.xrun_seg_sound XCuts.z684 XCuts.b684 XCuts.z685 XCuts.b685 XCuts.n684 XCuts.v684 eq_refl XJ0684.seg).
Definition k685 := XR_trans _ _ _ _ _ _ _ _ _ _ k684 (XTop.xrun_seg_sound XCuts.z685 XCuts.b685 XCuts.z686 XCuts.b686 XCuts.n685 XCuts.v685 eq_refl XJ0685.seg).
Definition k686 := XR_trans _ _ _ _ _ _ _ _ _ _ k685 (XTop.xrun_seg_sound XCuts.z686 XCuts.b686 XCuts.z687 XCuts.b687 XCuts.n686 XCuts.v686 eq_refl XJ0686.seg).
Definition k687 := XR_trans _ _ _ _ _ _ _ _ _ _ k686 (XTop.xrun_seg_sound XCuts.z687 XCuts.b687 XCuts.z688 XCuts.b688 XCuts.n687 XCuts.v687 eq_refl XJ0687.seg).
Definition k688 := XR_trans _ _ _ _ _ _ _ _ _ _ k687 (XTop.xrun_seg_sound XCuts.z688 XCuts.b688 XCuts.z689 XCuts.b689 XCuts.n688 XCuts.v688 eq_refl XJ0688.seg).
Definition k689 := XR_trans _ _ _ _ _ _ _ _ _ _ k688 (XTop.xrun_seg_sound XCuts.z689 XCuts.b689 XCuts.z690 XCuts.b690 XCuts.n689 XCuts.v689 eq_refl XJ0689.seg).
Definition k690 := XR_trans _ _ _ _ _ _ _ _ _ _ k689 (XTop.xrun_seg_sound XCuts.z690 XCuts.b690 XCuts.z691 XCuts.b691 XCuts.n690 XCuts.v690 eq_refl XJ0690.seg).
Definition k691 := XR_trans _ _ _ _ _ _ _ _ _ _ k690 (XTop.xrun_seg_sound XCuts.z691 XCuts.b691 XCuts.z692 XCuts.b692 XCuts.n691 XCuts.v691 eq_refl XJ0691.seg).
Definition k692 := XR_trans _ _ _ _ _ _ _ _ _ _ k691 (XTop.xrun_seg_sound XCuts.z692 XCuts.b692 XCuts.z693 XCuts.b693 XCuts.n692 XCuts.v692 eq_refl XJ0692.seg).
Definition k693 := XR_trans _ _ _ _ _ _ _ _ _ _ k692 (XTop.xrun_seg_sound XCuts.z693 XCuts.b693 XCuts.z694 XCuts.b694 XCuts.n693 XCuts.v693 eq_refl XJ0693.seg).
Definition k694 := XR_trans _ _ _ _ _ _ _ _ _ _ k693 (XTop.xrun_seg_sound XCuts.z694 XCuts.b694 XCuts.z695 XCuts.b695 XCuts.n694 XCuts.v694 eq_refl XJ0694.seg).
Definition k695 := XR_trans _ _ _ _ _ _ _ _ _ _ k694 (XTop.xrun_seg_sound XCuts.z695 XCuts.b695 XCuts.z696 XCuts.b696 XCuts.n695 XCuts.v695 eq_refl XJ0695.seg).
Definition k696 := XR_trans _ _ _ _ _ _ _ _ _ _ k695 (XTop.xrun_seg_sound XCuts.z696 XCuts.b696 XCuts.z697 XCuts.b697 XCuts.n696 XCuts.v696 eq_refl XJ0696.seg).
Definition k697 := XR_trans _ _ _ _ _ _ _ _ _ _ k696 (XTop.xrun_seg_sound XCuts.z697 XCuts.b697 XCuts.z698 XCuts.b698 XCuts.n697 XCuts.v697 eq_refl XJ0697.seg).
Definition k698 := XR_trans _ _ _ _ _ _ _ _ _ _ k697 (XTop.xrun_seg_sound XCuts.z698 XCuts.b698 XCuts.z699 XCuts.b699 XCuts.n698 XCuts.v698 eq_refl XJ0698.seg).
Definition k699 := XR_trans _ _ _ _ _ _ _ _ _ _ k698 (XTop.xrun_seg_sound XCuts.z699 XCuts.b699 XCuts.z700 XCuts.b700 XCuts.n699 XCuts.v699 eq_refl XJ0699.seg).
Definition k700 := XR_trans _ _ _ _ _ _ _ _ _ _ k699 (XTop.xrun_seg_sound XCuts.z700 XCuts.b700 XCuts.z701 XCuts.b701 XCuts.n700 XCuts.v700 eq_refl XJ0700.seg).
Definition k701 := XR_trans _ _ _ _ _ _ _ _ _ _ k700 (XTop.xrun_seg_sound XCuts.z701 XCuts.b701 XCuts.z702 XCuts.b702 XCuts.n701 XCuts.v701 eq_refl XJ0701.seg).
Definition k702 := XR_trans _ _ _ _ _ _ _ _ _ _ k701 (XTop.xrun_seg_sound XCuts.z702 XCuts.b702 XCuts.z703 XCuts.b703 XCuts.n702 XCuts.v702 eq_refl XJ0702.seg).
Definition k703 := XR_trans _ _ _ _ _ _ _ _ _ _ k702 (XTop.xrun_seg_sound XCuts.z703 XCuts.b703 XCuts.z704 XCuts.b704 XCuts.n703 XCuts.v703 eq_refl XJ0703.seg).
Definition k704 := XR_trans _ _ _ _ _ _ _ _ _ _ k703 (XTop.xrun_seg_sound XCuts.z704 XCuts.b704 XCuts.z705 XCuts.b705 XCuts.n704 XCuts.v704 eq_refl XJ0704.seg).
Definition k705 := XR_trans _ _ _ _ _ _ _ _ _ _ k704 (XTop.xrun_seg_sound XCuts.z705 XCuts.b705 XCuts.z706 XCuts.b706 XCuts.n705 XCuts.v705 eq_refl XJ0705.seg).
Definition korbit := XR_trans _ _ _ _ _ _ _ _ _ _ k705
  (XTop.xrun_halt_at_sound XCuts.z706 XCuts.b706 XCuts.y_end XCuts.a_halt XCuts.nh XCuts.vh eq_refl XJHalt.seg).

Lemma orbit_n : Num.val XCuts.n0 + Num.val XCuts.n1 + Num.val XCuts.n2 + Num.val XCuts.n3 + Num.val XCuts.n4 + Num.val XCuts.n5 + Num.val XCuts.n6 + Num.val XCuts.n7 + Num.val XCuts.n8 + Num.val XCuts.n9 + Num.val XCuts.n10 + Num.val XCuts.n11 + Num.val XCuts.n12 + Num.val XCuts.n13 + Num.val XCuts.n14 + Num.val XCuts.n15 + Num.val XCuts.n16 + Num.val XCuts.n17 + Num.val XCuts.n18 + Num.val XCuts.n19 + Num.val XCuts.n20 + Num.val XCuts.n21 + Num.val XCuts.n22 + Num.val XCuts.n23 + Num.val XCuts.n24 + Num.val XCuts.n25 + Num.val XCuts.n26 + Num.val XCuts.n27 + Num.val XCuts.n28 + Num.val XCuts.n29 + Num.val XCuts.n30 + Num.val XCuts.n31 + Num.val XCuts.n32 + Num.val XCuts.n33 + Num.val XCuts.n34 + Num.val XCuts.n35 + Num.val XCuts.n36 + Num.val XCuts.n37 + Num.val XCuts.n38 + Num.val XCuts.n39 + Num.val XCuts.n40 + Num.val XCuts.n41 + Num.val XCuts.n42 + Num.val XCuts.n43 + Num.val XCuts.n44 + Num.val XCuts.n45 + Num.val XCuts.n46 + Num.val XCuts.n47 + Num.val XCuts.n48 + Num.val XCuts.n49 + Num.val XCuts.n50 + Num.val XCuts.n51 + Num.val XCuts.n52 + Num.val XCuts.n53 + Num.val XCuts.n54 + Num.val XCuts.n55 + Num.val XCuts.n56 + Num.val XCuts.n57 + Num.val XCuts.n58 + Num.val XCuts.n59 + Num.val XCuts.n60 + Num.val XCuts.n61 + Num.val XCuts.n62 + Num.val XCuts.n63 + Num.val XCuts.n64 + Num.val XCuts.n65 + Num.val XCuts.n66 + Num.val XCuts.n67 + Num.val XCuts.n68 + Num.val XCuts.n69 + Num.val XCuts.n70 + Num.val XCuts.n71 + Num.val XCuts.n72 + Num.val XCuts.n73 + Num.val XCuts.n74 + Num.val XCuts.n75 + Num.val XCuts.n76 + Num.val XCuts.n77 + Num.val XCuts.n78 + Num.val XCuts.n79 + Num.val XCuts.n80 + Num.val XCuts.n81 + Num.val XCuts.n82 + Num.val XCuts.n83 + Num.val XCuts.n84 + Num.val XCuts.n85 + Num.val XCuts.n86 + Num.val XCuts.n87 + Num.val XCuts.n88 + Num.val XCuts.n89 + Num.val XCuts.n90 + Num.val XCuts.n91 + Num.val XCuts.n92 + Num.val XCuts.n93 + Num.val XCuts.n94 + Num.val XCuts.n95 + Num.val XCuts.n96 + Num.val XCuts.n97 + Num.val XCuts.n98 + Num.val XCuts.n99 + Num.val XCuts.n100 + Num.val XCuts.n101 + Num.val XCuts.n102 + Num.val XCuts.n103 + Num.val XCuts.n104 + Num.val XCuts.n105 + Num.val XCuts.n106 + Num.val XCuts.n107 + Num.val XCuts.n108 + Num.val XCuts.n109 + Num.val XCuts.n110 + Num.val XCuts.n111 + Num.val XCuts.n112 + Num.val XCuts.n113 + Num.val XCuts.n114 + Num.val XCuts.n115 + Num.val XCuts.n116 + Num.val XCuts.n117 + Num.val XCuts.n118 + Num.val XCuts.n119 + Num.val XCuts.n120 + Num.val XCuts.n121 + Num.val XCuts.n122 + Num.val XCuts.n123 + Num.val XCuts.n124 + Num.val XCuts.n125 + Num.val XCuts.n126 + Num.val XCuts.n127 + Num.val XCuts.n128 + Num.val XCuts.n129 + Num.val XCuts.n130 + Num.val XCuts.n131 + Num.val XCuts.n132 + Num.val XCuts.n133 + Num.val XCuts.n134 + Num.val XCuts.n135 + Num.val XCuts.n136 + Num.val XCuts.n137 + Num.val XCuts.n138 + Num.val XCuts.n139 + Num.val XCuts.n140 + Num.val XCuts.n141 + Num.val XCuts.n142 + Num.val XCuts.n143 + Num.val XCuts.n144 + Num.val XCuts.n145 + Num.val XCuts.n146 + Num.val XCuts.n147 + Num.val XCuts.n148 + Num.val XCuts.n149 + Num.val XCuts.n150 + Num.val XCuts.n151 + Num.val XCuts.n152 + Num.val XCuts.n153 + Num.val XCuts.n154 + Num.val XCuts.n155 + Num.val XCuts.n156 + Num.val XCuts.n157 + Num.val XCuts.n158 + Num.val XCuts.n159 + Num.val XCuts.n160 + Num.val XCuts.n161 + Num.val XCuts.n162 + Num.val XCuts.n163 + Num.val XCuts.n164 + Num.val XCuts.n165 + Num.val XCuts.n166 + Num.val XCuts.n167 + Num.val XCuts.n168 + Num.val XCuts.n169 + Num.val XCuts.n170 + Num.val XCuts.n171 + Num.val XCuts.n172 + Num.val XCuts.n173 + Num.val XCuts.n174 + Num.val XCuts.n175 + Num.val XCuts.n176 + Num.val XCuts.n177 + Num.val XCuts.n178 + Num.val XCuts.n179 + Num.val XCuts.n180 + Num.val XCuts.n181 + Num.val XCuts.n182 + Num.val XCuts.n183 + Num.val XCuts.n184 + Num.val XCuts.n185 + Num.val XCuts.n186 + Num.val XCuts.n187 + Num.val XCuts.n188 + Num.val XCuts.n189 + Num.val XCuts.n190 + Num.val XCuts.n191 + Num.val XCuts.n192 + Num.val XCuts.n193 + Num.val XCuts.n194 + Num.val XCuts.n195 + Num.val XCuts.n196 + Num.val XCuts.n197 + Num.val XCuts.n198 + Num.val XCuts.n199 + Num.val XCuts.n200 + Num.val XCuts.n201 + Num.val XCuts.n202 + Num.val XCuts.n203 + Num.val XCuts.n204 + Num.val XCuts.n205 + Num.val XCuts.n206 + Num.val XCuts.n207 + Num.val XCuts.n208 + Num.val XCuts.n209 + Num.val XCuts.n210 + Num.val XCuts.n211 + Num.val XCuts.n212 + Num.val XCuts.n213 + Num.val XCuts.n214 + Num.val XCuts.n215 + Num.val XCuts.n216 + Num.val XCuts.n217 + Num.val XCuts.n218 + Num.val XCuts.n219 + Num.val XCuts.n220 + Num.val XCuts.n221 + Num.val XCuts.n222 + Num.val XCuts.n223 + Num.val XCuts.n224 + Num.val XCuts.n225 + Num.val XCuts.n226 + Num.val XCuts.n227 + Num.val XCuts.n228 + Num.val XCuts.n229 + Num.val XCuts.n230 + Num.val XCuts.n231 + Num.val XCuts.n232 + Num.val XCuts.n233 + Num.val XCuts.n234 + Num.val XCuts.n235 + Num.val XCuts.n236 + Num.val XCuts.n237 + Num.val XCuts.n238 + Num.val XCuts.n239 + Num.val XCuts.n240 + Num.val XCuts.n241 + Num.val XCuts.n242 + Num.val XCuts.n243 + Num.val XCuts.n244 + Num.val XCuts.n245 + Num.val XCuts.n246 + Num.val XCuts.n247 + Num.val XCuts.n248 + Num.val XCuts.n249 + Num.val XCuts.n250 + Num.val XCuts.n251 + Num.val XCuts.n252 + Num.val XCuts.n253 + Num.val XCuts.n254 + Num.val XCuts.n255 + Num.val XCuts.n256 + Num.val XCuts.n257 + Num.val XCuts.n258 + Num.val XCuts.n259 + Num.val XCuts.n260 + Num.val XCuts.n261 + Num.val XCuts.n262 + Num.val XCuts.n263 + Num.val XCuts.n264 + Num.val XCuts.n265 + Num.val XCuts.n266 + Num.val XCuts.n267 + Num.val XCuts.n268 + Num.val XCuts.n269 + Num.val XCuts.n270 + Num.val XCuts.n271 + Num.val XCuts.n272 + Num.val XCuts.n273 + Num.val XCuts.n274 + Num.val XCuts.n275 + Num.val XCuts.n276 + Num.val XCuts.n277 + Num.val XCuts.n278 + Num.val XCuts.n279 + Num.val XCuts.n280 + Num.val XCuts.n281 + Num.val XCuts.n282 + Num.val XCuts.n283 + Num.val XCuts.n284 + Num.val XCuts.n285 + Num.val XCuts.n286 + Num.val XCuts.n287 + Num.val XCuts.n288 + Num.val XCuts.n289 + Num.val XCuts.n290 + Num.val XCuts.n291 + Num.val XCuts.n292 + Num.val XCuts.n293 + Num.val XCuts.n294 + Num.val XCuts.n295 + Num.val XCuts.n296 + Num.val XCuts.n297 + Num.val XCuts.n298 + Num.val XCuts.n299 + Num.val XCuts.n300 + Num.val XCuts.n301 + Num.val XCuts.n302 + Num.val XCuts.n303 + Num.val XCuts.n304 + Num.val XCuts.n305 + Num.val XCuts.n306 + Num.val XCuts.n307 + Num.val XCuts.n308 + Num.val XCuts.n309 + Num.val XCuts.n310 + Num.val XCuts.n311 + Num.val XCuts.n312 + Num.val XCuts.n313 + Num.val XCuts.n314 + Num.val XCuts.n315 + Num.val XCuts.n316 + Num.val XCuts.n317 + Num.val XCuts.n318 + Num.val XCuts.n319 + Num.val XCuts.n320 + Num.val XCuts.n321 + Num.val XCuts.n322 + Num.val XCuts.n323 + Num.val XCuts.n324 + Num.val XCuts.n325 + Num.val XCuts.n326 + Num.val XCuts.n327 + Num.val XCuts.n328 + Num.val XCuts.n329 + Num.val XCuts.n330 + Num.val XCuts.n331 + Num.val XCuts.n332 + Num.val XCuts.n333 + Num.val XCuts.n334 + Num.val XCuts.n335 + Num.val XCuts.n336 + Num.val XCuts.n337 + Num.val XCuts.n338 + Num.val XCuts.n339 + Num.val XCuts.n340 + Num.val XCuts.n341 + Num.val XCuts.n342 + Num.val XCuts.n343 + Num.val XCuts.n344 + Num.val XCuts.n345 + Num.val XCuts.n346 + Num.val XCuts.n347 + Num.val XCuts.n348 + Num.val XCuts.n349 + Num.val XCuts.n350 + Num.val XCuts.n351 + Num.val XCuts.n352 + Num.val XCuts.n353 + Num.val XCuts.n354 + Num.val XCuts.n355 + Num.val XCuts.n356 + Num.val XCuts.n357 + Num.val XCuts.n358 + Num.val XCuts.n359 + Num.val XCuts.n360 + Num.val XCuts.n361 + Num.val XCuts.n362 + Num.val XCuts.n363 + Num.val XCuts.n364 + Num.val XCuts.n365 + Num.val XCuts.n366 + Num.val XCuts.n367 + Num.val XCuts.n368 + Num.val XCuts.n369 + Num.val XCuts.n370 + Num.val XCuts.n371 + Num.val XCuts.n372 + Num.val XCuts.n373 + Num.val XCuts.n374 + Num.val XCuts.n375 + Num.val XCuts.n376 + Num.val XCuts.n377 + Num.val XCuts.n378 + Num.val XCuts.n379 + Num.val XCuts.n380 + Num.val XCuts.n381 + Num.val XCuts.n382 + Num.val XCuts.n383 + Num.val XCuts.n384 + Num.val XCuts.n385 + Num.val XCuts.n386 + Num.val XCuts.n387 + Num.val XCuts.n388 + Num.val XCuts.n389 + Num.val XCuts.n390 + Num.val XCuts.n391 + Num.val XCuts.n392 + Num.val XCuts.n393 + Num.val XCuts.n394 + Num.val XCuts.n395 + Num.val XCuts.n396 + Num.val XCuts.n397 + Num.val XCuts.n398 + Num.val XCuts.n399 + Num.val XCuts.n400 + Num.val XCuts.n401 + Num.val XCuts.n402 + Num.val XCuts.n403 + Num.val XCuts.n404 + Num.val XCuts.n405 + Num.val XCuts.n406 + Num.val XCuts.n407 + Num.val XCuts.n408 + Num.val XCuts.n409 + Num.val XCuts.n410 + Num.val XCuts.n411 + Num.val XCuts.n412 + Num.val XCuts.n413 + Num.val XCuts.n414 + Num.val XCuts.n415 + Num.val XCuts.n416 + Num.val XCuts.n417 + Num.val XCuts.n418 + Num.val XCuts.n419 + Num.val XCuts.n420 + Num.val XCuts.n421 + Num.val XCuts.n422 + Num.val XCuts.n423 + Num.val XCuts.n424 + Num.val XCuts.n425 + Num.val XCuts.n426 + Num.val XCuts.n427 + Num.val XCuts.n428 + Num.val XCuts.n429 + Num.val XCuts.n430 + Num.val XCuts.n431 + Num.val XCuts.n432 + Num.val XCuts.n433 + Num.val XCuts.n434 + Num.val XCuts.n435 + Num.val XCuts.n436 + Num.val XCuts.n437 + Num.val XCuts.n438 + Num.val XCuts.n439 + Num.val XCuts.n440 + Num.val XCuts.n441 + Num.val XCuts.n442 + Num.val XCuts.n443 + Num.val XCuts.n444 + Num.val XCuts.n445 + Num.val XCuts.n446 + Num.val XCuts.n447 + Num.val XCuts.n448 + Num.val XCuts.n449 + Num.val XCuts.n450 + Num.val XCuts.n451 + Num.val XCuts.n452 + Num.val XCuts.n453 + Num.val XCuts.n454 + Num.val XCuts.n455 + Num.val XCuts.n456 + Num.val XCuts.n457 + Num.val XCuts.n458 + Num.val XCuts.n459 + Num.val XCuts.n460 + Num.val XCuts.n461 + Num.val XCuts.n462 + Num.val XCuts.n463 + Num.val XCuts.n464 + Num.val XCuts.n465 + Num.val XCuts.n466 + Num.val XCuts.n467 + Num.val XCuts.n468 + Num.val XCuts.n469 + Num.val XCuts.n470 + Num.val XCuts.n471 + Num.val XCuts.n472 + Num.val XCuts.n473 + Num.val XCuts.n474 + Num.val XCuts.n475 + Num.val XCuts.n476 + Num.val XCuts.n477 + Num.val XCuts.n478 + Num.val XCuts.n479 + Num.val XCuts.n480 + Num.val XCuts.n481 + Num.val XCuts.n482 + Num.val XCuts.n483 + Num.val XCuts.n484 + Num.val XCuts.n485 + Num.val XCuts.n486 + Num.val XCuts.n487 + Num.val XCuts.n488 + Num.val XCuts.n489 + Num.val XCuts.n490 + Num.val XCuts.n491 + Num.val XCuts.n492 + Num.val XCuts.n493 + Num.val XCuts.n494 + Num.val XCuts.n495 + Num.val XCuts.n496 + Num.val XCuts.n497 + Num.val XCuts.n498 + Num.val XCuts.n499 + Num.val XCuts.n500 + Num.val XCuts.n501 + Num.val XCuts.n502 + Num.val XCuts.n503 + Num.val XCuts.n504 + Num.val XCuts.n505 + Num.val XCuts.n506 + Num.val XCuts.n507 + Num.val XCuts.n508 + Num.val XCuts.n509 + Num.val XCuts.n510 + Num.val XCuts.n511 + Num.val XCuts.n512 + Num.val XCuts.n513 + Num.val XCuts.n514 + Num.val XCuts.n515 + Num.val XCuts.n516 + Num.val XCuts.n517 + Num.val XCuts.n518 + Num.val XCuts.n519 + Num.val XCuts.n520 + Num.val XCuts.n521 + Num.val XCuts.n522 + Num.val XCuts.n523 + Num.val XCuts.n524 + Num.val XCuts.n525 + Num.val XCuts.n526 + Num.val XCuts.n527 + Num.val XCuts.n528 + Num.val XCuts.n529 + Num.val XCuts.n530 + Num.val XCuts.n531 + Num.val XCuts.n532 + Num.val XCuts.n533 + Num.val XCuts.n534 + Num.val XCuts.n535 + Num.val XCuts.n536 + Num.val XCuts.n537 + Num.val XCuts.n538 + Num.val XCuts.n539 + Num.val XCuts.n540 + Num.val XCuts.n541 + Num.val XCuts.n542 + Num.val XCuts.n543 + Num.val XCuts.n544 + Num.val XCuts.n545 + Num.val XCuts.n546 + Num.val XCuts.n547 + Num.val XCuts.n548 + Num.val XCuts.n549 + Num.val XCuts.n550 + Num.val XCuts.n551 + Num.val XCuts.n552 + Num.val XCuts.n553 + Num.val XCuts.n554 + Num.val XCuts.n555 + Num.val XCuts.n556 + Num.val XCuts.n557 + Num.val XCuts.n558 + Num.val XCuts.n559 + Num.val XCuts.n560 + Num.val XCuts.n561 + Num.val XCuts.n562 + Num.val XCuts.n563 + Num.val XCuts.n564 + Num.val XCuts.n565 + Num.val XCuts.n566 + Num.val XCuts.n567 + Num.val XCuts.n568 + Num.val XCuts.n569 + Num.val XCuts.n570 + Num.val XCuts.n571 + Num.val XCuts.n572 + Num.val XCuts.n573 + Num.val XCuts.n574 + Num.val XCuts.n575 + Num.val XCuts.n576 + Num.val XCuts.n577 + Num.val XCuts.n578 + Num.val XCuts.n579 + Num.val XCuts.n580 + Num.val XCuts.n581 + Num.val XCuts.n582 + Num.val XCuts.n583 + Num.val XCuts.n584 + Num.val XCuts.n585 + Num.val XCuts.n586 + Num.val XCuts.n587 + Num.val XCuts.n588 + Num.val XCuts.n589 + Num.val XCuts.n590 + Num.val XCuts.n591 + Num.val XCuts.n592 + Num.val XCuts.n593 + Num.val XCuts.n594 + Num.val XCuts.n595 + Num.val XCuts.n596 + Num.val XCuts.n597 + Num.val XCuts.n598 + Num.val XCuts.n599 + Num.val XCuts.n600 + Num.val XCuts.n601 + Num.val XCuts.n602 + Num.val XCuts.n603 + Num.val XCuts.n604 + Num.val XCuts.n605 + Num.val XCuts.n606 + Num.val XCuts.n607 + Num.val XCuts.n608 + Num.val XCuts.n609 + Num.val XCuts.n610 + Num.val XCuts.n611 + Num.val XCuts.n612 + Num.val XCuts.n613 + Num.val XCuts.n614 + Num.val XCuts.n615 + Num.val XCuts.n616 + Num.val XCuts.n617 + Num.val XCuts.n618 + Num.val XCuts.n619 + Num.val XCuts.n620 + Num.val XCuts.n621 + Num.val XCuts.n622 + Num.val XCuts.n623 + Num.val XCuts.n624 + Num.val XCuts.n625 + Num.val XCuts.n626 + Num.val XCuts.n627 + Num.val XCuts.n628 + Num.val XCuts.n629 + Num.val XCuts.n630 + Num.val XCuts.n631 + Num.val XCuts.n632 + Num.val XCuts.n633 + Num.val XCuts.n634 + Num.val XCuts.n635 + Num.val XCuts.n636 + Num.val XCuts.n637 + Num.val XCuts.n638 + Num.val XCuts.n639 + Num.val XCuts.n640 + Num.val XCuts.n641 + Num.val XCuts.n642 + Num.val XCuts.n643 + Num.val XCuts.n644 + Num.val XCuts.n645 + Num.val XCuts.n646 + Num.val XCuts.n647 + Num.val XCuts.n648 + Num.val XCuts.n649 + Num.val XCuts.n650 + Num.val XCuts.n651 + Num.val XCuts.n652 + Num.val XCuts.n653 + Num.val XCuts.n654 + Num.val XCuts.n655 + Num.val XCuts.n656 + Num.val XCuts.n657 + Num.val XCuts.n658 + Num.val XCuts.n659 + Num.val XCuts.n660 + Num.val XCuts.n661 + Num.val XCuts.n662 + Num.val XCuts.n663 + Num.val XCuts.n664 + Num.val XCuts.n665 + Num.val XCuts.n666 + Num.val XCuts.n667 + Num.val XCuts.n668 + Num.val XCuts.n669 + Num.val XCuts.n670 + Num.val XCuts.n671 + Num.val XCuts.n672 + Num.val XCuts.n673 + Num.val XCuts.n674 + Num.val XCuts.n675 + Num.val XCuts.n676 + Num.val XCuts.n677 + Num.val XCuts.n678 + Num.val XCuts.n679 + Num.val XCuts.n680 + Num.val XCuts.n681 + Num.val XCuts.n682 + Num.val XCuts.n683 + Num.val XCuts.n684 + Num.val XCuts.n685 + Num.val XCuts.n686 + Num.val XCuts.n687 + Num.val XCuts.n688 + Num.val XCuts.n689 + Num.val XCuts.n690 + Num.val XCuts.n691 + Num.val XCuts.n692 + Num.val XCuts.n693 + Num.val XCuts.n694 + Num.val XCuts.n695 + Num.val XCuts.n696 + Num.val XCuts.n697 + Num.val XCuts.n698 + Num.val XCuts.n699 + Num.val XCuts.n700 + Num.val XCuts.n701 + Num.val XCuts.n702 + Num.val XCuts.n703 + Num.val XCuts.n704 + Num.val XCuts.n705 + Num.val XCuts.nh = n_apps.
Proof. vm_compute. reflexivity. Qed.

Theorem bb6_holdout_steps : halts_in tm c0 n_steps.
Proof.
  refine (steps_of_orbit _ _ _ orbit_n _); [exact korbit|vm_compute; reflexivity].
Qed.

Print Assumptions bb6_holdout_steps.
