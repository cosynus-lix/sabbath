(set-logic QF_NRA)
(declare-fun _u1 () Real)
(declare-fun _k1 () Real)
(declare-fun _v2 () Real)
(declare-fun _m2 () Real)
(declare-fun _u10 () Real)
(declare-fun _k2 () Real)
(declare-fun _m1 () Real)
(declare-fun _u8 () Real)
(declare-fun _v1 () Real)
(declare-fun _x1 () Real)
(declare-fun _x2 () Real)


(define-fun .def_0 () Real (* 2.0 _k2 _m2 _u10))
(define-fun .def_1 () Real (* (- 1.0) _k2 _m1 _u8))
(define-fun .def_2 () Real (* _k2 _m2 _u8))
(define-fun .def_3 () Real (* _k1 _m2 _u8))
(define-fun .def_4 () Real (+ .def_3 .def_2 .def_1 .def_0))
(define-fun .def_5 () Real (/ 1.0 _m1))
(define-fun .def_6 () Real (/ 1.0 _k2))
(define-fun .def_7 () Real (* (- 1.0) _v2 .def_6 .def_5 .def_4))
(define-fun .def_8 () Real (* (- 1.0) _u8 _v1))
(define-fun .def_9 () Real (+ .def_8 .def_7))
(define-fun .def_10 () Real (* (- 1.0) _x1))

(define-fun .def_11 () Real (+ _x2 .def_10))
(define-fun .def_12 () Real (/ 1.0 _m2))
(define-fun .def_13 () Real (* (- 1.0) _k2 .def_12 .def_11 .def_9))
(define-fun .def_14 () Real (* (- 1.0) _x2))
(define-fun .def_15 () Real (+ _x1 .def_14))
(define-fun .def_16 () Real (* (- 1.0) _k2 .def_5 .def_15))
(define-fun .def_17 () Real (* (- 1.0) _k1 _x1 .def_5))
(define-fun .def_18 () Real (+ .def_17 .def_16))
(define-fun .def_19 () Real (* (- 2.0) _u10 _v1))
(define-fun .def_20 () Real (* (- 1.0) _u8 _v2))

(define-fun .def_21 () Real  (+ .def_20 .def_19))
(define-fun .def_22 () Real  (* .def_21 .def_18))
(define-fun .def_23 () Real  (* (- 2.0) _m2 _u10))
(define-fun .def_24 () Real  (* _m1 _u8))
(define-fun .def_25 () Real  (+ .def_24 .def_23))
(define-fun .def_26 () Real  (* (- 1.0) _k2 _x1 .def_5 .def_12 .def_25))
(define-fun .def_27 () Real  (+ .def_3 .def_1 .def_0))
(define-fun .def_28 () Real  (* (- 1.0) _x2 .def_5 .def_12 .def_27))
(define-fun .def_29 () Real  (+ .def_28 .def_26))
(define-fun .def_30 () Real  (* _v2 .def_29))

(define-fun .def_31 () Real (* (- 1.0) _k2 _x2 .def_5 .def_12 .def_25))
(define-fun .def_32 () Real (* 2.0 _k1 _m2 _u10))
(define-fun .def_33 () Real (+ .def_1 .def_32 .def_0))
(define-fun .def_34 () Real (* (- 1.0) _x1 .def_5 .def_12 .def_33))
(define-fun .def_35 () Real (+ .def_34 .def_31))
(define-fun .def_36 () Real (* _v1 .def_35))
(define-fun .def_37 () Real (+ .def_36 .def_30 .def_22 .def_13))
(define-fun .def_38 () Bool (= .def_37 0.0))
(define-fun .def_39 () Real (* _m2 _m1))
(define-fun .def_40 () Real (* 2.0 _m2 _u10 _k2))

(define-fun .def_41 () Real (* _k2 _m1 _u8))
(define-fun .def_42 () Real (- .def_3 .def_41))
(define-fun .def_43 () Real (+ .def_42 .def_40))
(define-fun .def_44 () Real (* (/ 1 2) _x2 _x2 .def_43))
(define-fun .def_45 () Real (/ .def_44 .def_39))
(define-fun .def_46 () Real (- .def_32 .def_41))
(define-fun .def_47 () Real (+ .def_46 .def_40))
(define-fun .def_48 () Real (* (/ 1 2) _x1 _x1 .def_47))
(define-fun .def_49 () Real (/ .def_48 .def_39))
(define-fun .def_50 () Real (* _k2 _m1))

(define-fun .def_51 () Real (* _m2 _k2 _u8))
(define-fun .def_52 () Real (+ .def_42 .def_51))
(define-fun .def_53 () Real (+ .def_52 .def_40))
(define-fun .def_54 () Real (* (/ 1 2) _v2 _v2 .def_53))
(define-fun .def_55 () Real (/ .def_54 .def_50))
(define-fun .def_56 () Real (* _u10 _v1 _v1))
(define-fun .def_57 () Real (* 2.0 _m2 _u10))
(define-fun .def_58 () Real (- .def_24 .def_57))
(define-fun .def_59 () Real (* _x1 _x2 _k2 .def_58))

(define-fun .def_60 () Real (/ .def_59 .def_39))
(define-fun .def_61 () Real (* _v2 _u8 _v1))
(define-fun .def_62 () Real (+ .def_61 .def_60))
(define-fun .def_63 () Real (+ .def_62 .def_56))
(define-fun .def_64 () Real (+ .def_63 _u1))
(define-fun .def_65 () Real (+ .def_64 .def_55))
(define-fun .def_66 () Real (+ .def_65 .def_49))
(define-fun .def_67 () Real (+ .def_66 .def_45))
(define-fun .def_68 () Real (- 0.0 .def_67))
(define-fun .def_69 () Bool (= .def_68 0.0))

(define-fun .def_71 () Real (+ .def_3 .def_51 .def_1 .def_40))
(define-fun .def_72 () Real (* (- 1.0) _v2 .def_5 .def_6 .def_71))
(define-fun .def_73 () Real (+ .def_8 .def_72))
(define-fun .def_74 () Real (* (- 1.0) _k2 .def_12 .def_11 .def_73))
(define-fun .def_75 () Real (* (- 1.0) _v2 _u8))
(define-fun .def_76 () Real (+ .def_75 .def_19))
(define-fun .def_77 () Real (* (- 1.0) _x1 _k1 .def_5))
(define-fun .def_78 () Real (+ .def_77 .def_16))
(define-fun .def_79 () Real (* .def_78 .def_76))

(define-fun .def_80 () Real (* (- 1.0) _x1 _k2 .def_5 .def_12 .def_25))
(define-fun .def_81 () Real (+ .def_3 .def_1 .def_40))
(define-fun .def_82 () Real (* (- 1.0) _x2 .def_5 .def_12 .def_81))
(define-fun .def_83 () Real (+ .def_82 .def_80))
(define-fun .def_84 () Real (* _v2 .def_83))
(define-fun .def_85 () Real (* (- 1.0) _x2 _k2 .def_5 .def_12 .def_25))
(define-fun .def_86 () Real (+ .def_1 .def_32 .def_40))
(define-fun .def_87 () Real (* (- 1.0) _x1 .def_5 .def_12 .def_86))
(define-fun .def_88 () Real (+ .def_87 .def_85))
(define-fun .def_89 () Real (* _v1 .def_88))

(define-fun .def_90 () Real (+ .def_89 .def_84 .def_79 .def_74))
(define-fun .def_91 () Bool (< 0.0 .def_90))
(define-fun .def_92 () Bool (and .def_91 .def_69))
(define-fun .def_93 () Bool (< 0.0 .def_68))

(define-fun .def_95 () Bool (or (or .def_93 .def_92) (and .def_69 .def_38) ))

(define-fun .def_96 () Real (* _v2 .def_6 .def_5 .def_4))
(define-fun .def_97 () Real (* _u8 _v1))
(define-fun .def_98 () Real (+ .def_97 .def_96))
(define-fun .def_99 () Real (* (- 1.0) _k2 .def_12 .def_11 .def_98))

(define-fun .def_100 () Real (* 2.0 _u10 _v1))
(define-fun .def_101 () Real (* _u8 _v2))
(define-fun .def_102 () Real (+ .def_101 .def_100))
(define-fun .def_103 () Real (* .def_102 .def_18))
(define-fun .def_104 () Real (* _k2 _x1 .def_5 .def_12 .def_25))
(define-fun .def_105 () Real (* _x2 .def_5 .def_12 .def_27))
(define-fun .def_106 () Real (+ .def_105 .def_104))
(define-fun .def_107 () Real (* _v2 .def_106))
(define-fun .def_108 () Real (* _k2 _x2 .def_5 .def_12 .def_25))
(define-fun .def_109 () Real (* _x1 .def_5 .def_12 .def_33))

(define-fun .def_110 () Real (+ .def_109 .def_108))
(define-fun .def_111 () Real (* _v1 .def_110))
(define-fun .def_112 () Real (+ .def_111 .def_107 .def_103 .def_99))
(define-fun .def_113 () Bool (= .def_112 0.0))
(define-fun .def_114 () Bool (= .def_67 0.0))

(define-fun .def_115 () Bool (and .def_114 .def_113))

(define-fun .def_116 () Real (* _v2 .def_5 .def_6 .def_71))
(define-fun .def_117 () Real (+ .def_97 .def_116))
(define-fun .def_118 () Real (* (- 1.0) _k2 .def_12 .def_11 .def_117))
(define-fun .def_119 () Real (* _v2 _u8))

(define-fun .def_120 () Real (+ .def_119 .def_100))
(define-fun .def_121 () Real (* .def_78 .def_120))
(define-fun .def_122 () Real (* _x1 _k2 .def_5 .def_12 .def_25))
(define-fun .def_123 () Real (* _x2 .def_5 .def_12 .def_81))
(define-fun .def_124 () Real (+ .def_123 .def_122))
(define-fun .def_125 () Real (* _v2 .def_124))
(define-fun .def_126 () Real (* _x2 _k2 .def_5 .def_12 .def_25))
(define-fun .def_127 () Real (* _x1 .def_5 .def_12 .def_86))
(define-fun .def_128 () Real (+ .def_127 .def_126))
(define-fun .def_129 () Real (* _v1 .def_128))

(define-fun .def_130 () Real (+ .def_129 .def_125 .def_121 .def_118))
(define-fun .def_131 () Bool (< 0.0 .def_130))
(define-fun .def_133 () Bool (< 0.0 .def_67))

(define-fun and_1 () Bool (or (or .def_133 (and .def_131 .def_114)) (and .def_114 .def_113)) )
(define-fun and_2 () Bool (or (or .def_93 .def_92) (and .def_69 .def_38)))

(define-fun .def_137 () Bool (and
 and_1
 and_2
 )
)


(define-fun .new_def_132 () Bool (and .def_131 .def_114))
(define-fun .new_def_133 () Bool (< 0.0 .def_67))
(define-fun .new_def_134 () Bool (or .new_def_133 .new_def_132))
(define-fun .new_def_135 () Bool (or .new_def_134 .def_115))
(define-fun .new_def_136 () Bool (and true .new_def_135))
(define-fun .new_def_137 () Bool (and .new_def_136 .def_95))
(define-fun .new_def_138 () Bool (or false .new_def_137))
(define-fun .new_def_139 () Real (* _m1 _m2))

(define-fun .new_def_140 () Real (* _x2 1.0))
(define-fun .new_def_141 () Real (* _x2 .new_def_140))
(define-fun .new_def_142 () Real (* 2.0 _k2))
(define-fun .new_def_143 () Real (* .new_def_142 _m2))
(define-fun .new_def_144 () Real (* .new_def_143 _u10))
(define-fun .new_def_145 () Real (* .def_50 _u8))
(define-fun .new_def_146 () Real (* _k1 _m2))
(define-fun .new_def_147 () Real (* .new_def_146 _u8))
(define-fun .new_def_148 () Real (- .new_def_147 .new_def_145))
(define-fun .new_def_149 () Real (+ .new_def_148 .new_def_144))

(define-fun .new_def_150 () Real (* (/ 1 2) .new_def_149))
(define-fun .new_def_151 () Real (* .new_def_150 .new_def_141))
(define-fun .new_def_152 () Real (/ .new_def_151 .new_def_139))
(define-fun .new_def_153 () Real (* _x1 1.0))
(define-fun .new_def_154 () Real (* _x1 .new_def_153))
(define-fun .new_def_155 () Real (* 2.0 _k1))
(define-fun .new_def_156 () Real (* .new_def_155 _m2))
(define-fun .new_def_157 () Real (* .new_def_156 _u10))
(define-fun .new_def_158 () Real (- .new_def_157 .new_def_145))
(define-fun .new_def_159 () Real (+ .new_def_158 .new_def_144))

(define-fun .new_def_160 () Real (* (/ 1 2) .new_def_159))
(define-fun .new_def_161 () Real (* .new_def_160 .new_def_154))
(define-fun .new_def_162 () Real (/ .new_def_161 .new_def_139))
(define-fun .new_def_163 () Real (* _k2 _m2))
(define-fun .new_def_164 () Real (* .new_def_163 _u8))
(define-fun .new_def_165 () Real (+ .new_def_148 .new_def_164))
(define-fun .new_def_166 () Real (+ .new_def_165 .new_def_144))
(define-fun .new_def_167 () Real (* _v2 1.0))
(define-fun .new_def_168 () Real (* _v2 .new_def_167))
(define-fun .new_def_169 () Real (* (/ 1 2) .new_def_168))

(define-fun .new_def_170 () Real (* .new_def_169 .new_def_166))
(define-fun .new_def_171 () Real (/ .new_def_170 .def_50))
(define-fun .new_def_172 () Real (* _v1 1.0))
(define-fun .new_def_173 () Real (* _v1 .new_def_172))
(define-fun .new_def_174 () Real (* _u10 .new_def_173))
(define-fun .new_def_175 () Real (* 2.0 _m2))
(define-fun .new_def_176 () Real (* .new_def_175 _u10))
(define-fun .new_def_177 () Real (- .def_24 .new_def_176))
(define-fun .new_def_178 () Real (* _k2 _x1))
(define-fun .new_def_179 () Real (* .new_def_178 _x2))

(define-fun .new_def_180 () Real (* .new_def_179 .new_def_177))
(define-fun .new_def_181 () Real (/ .new_def_180 .new_def_139))
(define-fun .new_def_182 () Real (* .def_97 _v2))
(define-fun .new_def_183 () Real (+ .new_def_182 .new_def_181))
(define-fun .new_def_184 () Real (+ .new_def_183 .new_def_174))
(define-fun .new_def_185 () Real (+ .new_def_184 _u1))
(define-fun .new_def_186 () Real (+ .new_def_185 .new_def_171))
(define-fun .new_def_187 () Real (+ .new_def_186 .new_def_162))
(define-fun .new_def_188 () Real (+ .new_def_187 .new_def_152))

(define-fun leftdef () Bool
  (let ((.def_189 (= .new_def_188 0.0))) .def_189)
)

(define-fun formula () Bool (=> leftdef (and and_1 and_2)))
(define-fun _mod () Bool  (not formula))
;;(define-fun _mod () Bool (not (=> leftdef (and and_1 and_2))))


;; rhs
(assert _mod)
;; lhs
;; (assert .def_191)
(check-sat)
