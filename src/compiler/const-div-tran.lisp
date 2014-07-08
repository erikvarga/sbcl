;;;; Transforms specific to division when the divisor is a known constant

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!C")

;;; Note that all the integer division functions are available for
;;; inline expansion.

(macrolet ((deffrob (fun)
             `(define-source-transform ,fun (x &optional (y nil y-p))
                (declare (ignore y))
                (if y-p
                    (values nil t)
                    `(,',fun ,x 1)))))
  (deffrob truncate)
  (deffrob round)
  #-sb-xc-host ; (See CROSS-FLOAT-INFINITY-KLUDGE.)
  (deffrob floor)
  #-sb-xc-host ; (See CROSS-FLOAT-INFINITY-KLUDGE.)
  (deffrob ceiling))


;;;; converting special case divide to shifts

;;; These must come before the ones below, so that they are tried
;;; first.
(deftransform floor ((number divisor))
  `(multiple-value-bind (tru rem) (truncate number divisor)
     (if (and (not (zerop rem))
              (if (minusp divisor)
                  (plusp number)
                  (minusp number)))
         (values (1- tru) (+ rem divisor))
         (values tru rem))))

(deftransform ceiling ((number divisor))
  `(multiple-value-bind (tru rem) (truncate number divisor)
     (if (and (not (zerop rem))
              (if (minusp divisor)
                  (minusp number)
                  (plusp number)))
         (values (+ tru 1) (- rem divisor))
         (values tru rem))))

(deftransform rem ((number divisor))
  `(nth-value 1 (truncate number divisor)))

(deftransform mod ((number divisor))
  `(let ((rem (rem number divisor)))
     (if (and (not (zerop rem))
              (if (minusp divisor)
                  (plusp number)
                  (minusp number)))
         (+ rem divisor)
         rem))
)

;;; If arg is a constant power of two, turn FLOOR into a shift and
;;; mask. If CEILING, do FLOOR and correct the remainder and
;;; quotient.
(flet ((frob (y ceil-p)
         (unless (constant-lvar-p y)
           (give-up-ir1-transform))
         (let* ((y (lvar-value y))
                (y-abs (abs y))
                (len (1- (integer-length y-abs))))
           (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
             (give-up-ir1-transform))
           (let ((shift (- len))
                 (mask (1- y-abs))
                 (delta (if ceil-p y 0)))
             (if (minusp y)
                  `(let ((rem (- (logand (- x) ,mask))))
                     (values (- ,(if ceil-p '(if (zerop rem) 0 1) 0)
                                (+ (ash x ,shift)
                                   (if (zerop rem) 0 1)))
                             (- rem (if (zerop rem) 0 ,delta))))
                  `(let ((rem (logand x ,mask)))
                     (values (+ (ash x ,shift)
                                ,(if ceil-p '(if (zerop rem) 0 1) 0))
                             (- rem (if (zerop rem) 0 ,delta)))))))))
  (deftransform floor ((x y) (integer integer) *)
    "convert division by 2^k to shift"
    (frob y nil))
  (deftransform ceiling ((x y) (integer integer) *)
    "convert division by 2^k to shift"
    (frob y t)))

;;; Do the same for MOD.
(deftransform mod ((x y) (integer integer) *)
  "convert remainder mod 2^k to LOGAND"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let ((mask (1- y-abs)))
      (if (minusp y)
          `(- (logand (- x) ,mask))
          `(logand x ,mask)))))

;;; If arg is a constant power of two, turn TRUNCATE into a shift and mask.
(deftransform truncate ((x y) (integer integer))
  "convert division by 2^k to shift"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let* ((shift (- len))
           (mask (1- y-abs))
           (x-type (lvar-type x))
           (max-x  (or (and (numeric-type-p x-type)
                            (numeric-type-high x-type)) '*))
           (min-x  (or (and (numeric-type-p x-type)
                            (numeric-type-low x-type)) '*))
           (quot
            `(ash
              (truly-the (integer ,min-x ,max-x)
                         (+ x (if (minusp x) ,(1- y-abs) 0)))
              ,shift)))
      (when (minusp y) (setq quot `(- ,quot)))
      `(if (minusp x)
           (values ,quot
                   (- (logand (- x) ,mask)))
           (values ,quot
                   (logand x ,mask))))))

;;; And the same for REM.
(deftransform rem ((x y) (integer integer) *)
  "convert remainder mod 2^k to LOGAND"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let ((mask (1- y-abs)))
      `(if (minusp x)
           (- (logand (- x) ,mask))
           (logand x ,mask)))))


;;;; converting division to multiplication, addition, shift, etc.

;;; Get the multipy and shift value that can be used instead of
;;; dividing by y. Used in gen-(un)signed-div-by-constant-expr.
(defun choose-multiplier (y max-x)
  (let* ((max-shift (+ (integer-length max-x) (integer-length y)))
         (scale (ash 1 max-shift))
         (low (floor scale y))
         (k (1- (ceiling scale max-x)))
         (high (floor (+ scale k) y))
         (diff (logxor low high))
         (delta (1- (integer-length diff))))
    (values (ash high (- delta)) (- max-shift delta))))

;; Get the multiply and shift value for ceilinged and floored
;; division by y. Used in gen-ceilinged/floored-div-by-constant-expr.
(flet ((scale-down (multiplier shift)
         (let ((scale (min shift
                           (integer-length
                            (1- (logand multiplier
                                        (- multiplier)))))))
           (values (ash multiplier (- scale))
                   (- shift scale)))))
  (macrolet ((choose (neg-low neg-high pos-low pos-high)
               `(let* ((shift (+ precision (integer-length y)))
                       (mul-low (if negative-p ,neg-low ,pos-low))
                       (mul-high (if negative-p ,neg-high ,pos-high))
                       (shift-low shift)
                       (shift-high shift))
                  (multiple-value-setq (mul-low shift-low)
                    (scale-down mul-low shift-low))
                  (multiple-value-setq (mul-high shift-high)
                    (scale-down mul-high shift-high))
                  (if (< mul-low mul-high)
                      (values mul-low shift-low)
                      (values mul-high shift-high)))))
    (defun choose-ceiling-multiplier (y precision negative-p)
      (choose (1+ (floor (expt 2 shift) y))
              (floor (* (expt 2 shift)
                        (/ (1+ (expt 2 precision))
                           (* y (expt 2 precision)))))
              (ceiling (* (expt 2 shift)
                          (/ (1- (expt 2 precision))
                             (* y (expt 2 precision)))))
              (1- (ceiling (expt 2 shift) y))))
    (defun choose-floor-multiplier (y precision negative-p)
      (choose (1+ (floor (* (expt 2 shift)
                            (/ (1- (expt 2 precision))
                               (* y (expt 2 precision))))))
              (floor (expt 2 shift) y)
              (ceiling (expt 2 shift) y)
              (1- (ceiling (* (expt 2 shift)
                              (/ (1+ (expt 2 precision))
                                 (* y (expt 2 precision))))))))))

;;; Get the scaled multiply and shift value that can be used with
;;; multiply-high. Used in gen-(un)signed-div-by-constant-expr.
(defun get-scaled-multiplier (m shift)
  (let ((scale (max 0 (- sb!vm:n-word-bits shift))))
    (values (* m (ash 1 scale))
            (+ shift scale (- sb!vm:n-word-bits)))))

;;; Return an expression to calculate the integer quotient of X and
;;; constant Y, using multiplication, shift and add/sub instead of
;;; division. Both arguments must be unsigned, fit in a machine word and
;;; Y must neither be zero nor a power of two. The quotient is rounded
;;; towards zero.
;;; The algorithm is taken from the paper "Division by Invariant
;;; Integers using Multiplication", 1994 by Torbj\"{o}rn Granlund and
;;; Peter L. Montgomery, Figures 4.2 and 6.2, modified to exclude the
;;; case of division by powers of two.
;;; It is sometimes possible that all intermediate values fit in the
;;; word boundary, so there is no need to use multiply-high.  In these
;;; cases, use multiplication and shifting directly.
;;; Use a different algorithm for choosing the multiplier so that we can
;;; try direct multiplication first.  If multiply-high has to be used,
;;; the values can simply be scaled up.
;;; Also, for some reason, the paper prefers shifting to masking.  Mask
;;; instead.  Masking is equivalent to shifting right, then left again;
;;; all the intermediate values are still words, so we just have to shift
;;; right a bit more to compensate, at the end.
;;; Before resorting to multiplying by an n+1 bit constant, check if X+1
;;; still fits in n bits, and if so, use instead the multiply-add method
;;; described in the paper "N-Bit Unsigned Division Via N-Bit Multiply-Add",
;;; 2005 by Arch D. Robison.  Once again, use multiply-high only if
;;; multiplication and shifting cannot be done directly.
(defun gen-unsigned-div-by-constant-expr (y max-x optimize-fixnum-p)
  (declare (type (integer 3 #.most-positive-word) y)
           (type word max-x))
  (aver (not (zerop (logand y (1- y)))))
  (flet ((ld (x)
             ;; the floor of the binary logarithm of (positive) X
             (integer-length (1- x)))
         (shift-back (x)
           (ash x (- sb!vm::n-fixnum-tag-bits))))
    (let* ((x 'x)
           (n (expt 2 sb!vm:n-word-bits))
           (shift1 0)
           (expr (progn
      (multiple-value-bind (m shift2)
          (choose-multiplier y max-x)
        (when optimize-fixnum-p
          (when (< (* max-x m) n)
            ;; Don't optimize for fixnums if we
            ;; can use direct multiplication
            (return-from gen-unsigned-div-by-constant-expr
              (gen-unsigned-div-by-constant-expr y max-x nil)))
          (setq max-x (ash max-x sb!vm::n-fixnum-tag-bits))
          (setq x `(truly-the (integer 0 ,max-x)
                              (%fixnum-to-tagged-word x))))
        (cond
          ((< (* max-x m) n)
           `(ash (* ,x ,m) ,(- shift2)))
          (t
           (multiple-value-setq (m shift2)
             (get-scaled-multiplier m shift2))
           (when (and (>= m n) (evenp y))
             (setq shift1 (ld (logand y (- y))))
             (multiple-value-setq (m shift2)
               (multiple-value-call 'get-scaled-multiplier
                 (choose-multiplier (/ y (ash 1 shift1))
                                           (ash max-x (- shift1))))))
           (cond ((>= m n)
                  (cond ((< max-x (1- n))
                         (let* ((shift
                                (+ (integer-length max-x) (integer-length y) -1))
                                (m (floor (ash 1 shift) y)))
                           (cond ((< (* (1+ max-x) m) n)
                                  `(ash (* (+1 ,x) ,m) ,(- shift)))
                                 (t
                                  (let ((scale
                                         (max 0 (- sb!vm:n-word-bits shift))))
                                    `(ash (%multiply-high (1+ ,x)
                                                          ,(ash m scale))
                                          ,(- sb!vm:n-word-bits shift scale)))))))
                        (t
                         (flet ((word (x)
                                  `(truly-the word ,x)))
                           `(let* ((num ,x)
                                   (t1 (%multiply-high num ,(- m n))))
                              (ash ,(word `(+ t1 (ash ,(word `(- num t1))
                                                      -1)))
                                   ,(- 1 shift2)))))))
                 (t
                  `(ash (%multiply-high (logandc2 ,x ,(1- (ash 1 shift1))) ,m)
                        ,(- (+ shift1 shift2)))))))))))
      (if optimize-fixnum-p
          `(%tagged-word-to-fixnum
            (logandc2
             (%lose-word-derived-type ,expr)
             ,sb!vm:fixnum-tag-mask))
          expr))))

;;; The following two asserts show the expected average case and worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function, under a word size of 32 bits:
#+sb-xc-host
(when (= sb!vm:n-word-bits 32)
  (assert (equal (gen-unsigned-div-by-constant-expr 10 most-positive-word nil)
                 '(ash (%multiply-high (logandc2 x 0) 3435973837) -3)))
  (assert (equal (gen-unsigned-div-by-constant-expr 7 most-positive-word nil)
                  '(let* ((num x)
                          (t1 (%multiply-high num 613566757)))
                    (ash
                     (truly-the word
                      (+ t1 (ash (truly-the word (- num t1)) -1)))
                     -2)))))

;;; Return an expression for calculating the quotient like in the previous
;;; function, but the arguments have to fit in signed words.
;;; The algorithm is taken from the same paper, Figure 5.2
(defun gen-signed-div-by-constant-expr (y min-x max-x optimize-fixnum-p)
  (declare (type (or (integer #.(- (expt 2 (1- sb!vm:n-word-bits))) -3)
                     (integer 3 #.(expt 2 (1- sb!vm:n-word-bits)))) y)
           (type sb!vm:signed-word min-x max-x))
  (aver (not (zerop (logand (abs y) (1- (abs y))))))
  (aver (<= min-x max-x))
  (flet ((shift-back (x)
           (ash x (- sb!vm::n-fixnum-tag-bits))))
    (let ((n (expt 2 (1- sb!vm:n-word-bits))))
      (let ((expr
       (multiple-value-bind (m shift)
           (choose-multiplier (abs y) (max (abs max-x) (abs min-x)))
         (when optimize-fixnum-p
           (setq max-x (ash max-x sb!vm::n-fixnum-tag-bits)
                 min-x (ash min-x sb!vm::n-fixnum-tag-bits))
           (when (and
                  (<  (max (* (shift-back max-x) m)
                           (* (shift-back min-x) m)) n)
                  (>= (min (* (shift-back max-x) m)
                           (* (shift-back min-x) m)) (- n)))
             ;; Don't optimize for fixnums if we
             ;; can use direct multiplication
             (return-from gen-signed-div-by-constant-expr
               (gen-signed-div-by-constant-expr y
                                                (shift-back min-x)
                                                (shift-back max-x)
                                                nil))))
         (cond
           ((and (<  (max (* max-x m) (* min-x m)) n)
                 (>= (min (* max-x m) (* min-x m)) (- n)))
            `(ash (* num ,m) ,(- shift)))
           (t
            (multiple-value-setq (m shift)
              (get-scaled-multiplier m shift))
            (cond ((>= m n)
                   `(ash (truly-the
                          sb!vm:signed-word
                          (+ num
                             (%signed-multiply-high num ,(- m (* 2 n)))))
                         ,(- shift)))
                  (t
                   `(ash (%signed-multiply-high num ,m)
                         ,(- shift)))))))))
        (when optimize-fixnum-p
          (setq expr `(logandc2
                       (%lose-signed-word-derived-type ,expr)
                       ,sb!vm:fixnum-tag-mask)))
        (let ((x-sign-expr `(ash num ,(- sb!vm:n-word-bits))))
          (when optimize-fixnum-p
            (setq x-sign-expr
                  `(logandc2 (%lose-signed-word-derived-type ,x-sign-expr)
                             ,sb!vm:fixnum-tag-mask)))
          (setq expr `(- ,expr ,x-sign-expr)))
        (when optimize-fixnum-p
          (setq expr
                `(truly-the (integer ,(- 1 n) ,(1- n)) ,expr)))
        (when (minusp y)
          (setq expr `(- ,expr)))
        (let ((max (truncate max-x y))
              (min (truncate min-x y)))
          (when (minusp y) (rotatef min max))
          (setq expr
                (if optimize-fixnum-p
                    `(let ((num (truly-the (integer ,min-x ,max-x)
                                           (%fixnum-to-tagged-signed-word x))))
                       (truly-the (integer ,min ,max)
                                  (%tagged-signed-word-to-fixnum ,expr)))
                    `(let ((num x))
                       (truly-the (integer ,min ,max) ,expr)))))))))

;;; The following two asserts show the expected average case and worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function, under a word size of 32 bits:
#+sb-xc-host
(when (= sb!vm:n-word-bits 32)
  (assert (equal
           (gen-signed-div-by-constant-expr 11
                                            (- (expt 2 (1- sb!vm:n-word-bits)))
                                            (1- (expt 2 (1- sb!vm:n-word-bits)))
                                            nil)
           '(let ((num x))
             (truly-the (integer -195225786 195225786)
              (- (ash (%signed-multiply-high num 780903145) -1)
               (ash num -32))))))
  (assert (equal
           (gen-signed-div-by-constant-expr 7
                                            (- (expt 2 (1- sb!vm:n-word-bits)))
                                            (1- (expt 2 (1- sb!vm:n-word-bits)))
                                            nil)
           '(let ((num x))
             (truly-the (integer -306783378 306783378)
              (- (ash
                  (truly-the sb!vm:signed-word
                             (+ num (%signed-multiply-high num -1840700269)))
                  -2)
               (ash num -32)))))))

;;; Return an expression for calculating the quotient like in the previous
;;; function, but the quotient is rounded towards positive or negative infinity.
;;; The arguments can be either signed or unsigned words.
;;; The expression (CEILING X Y) is converted into and expression of the
;;; form (1+ (ASH (* X M) S)), and (FLOOR X Y) is converted into (ASH (* X M) S),
;;; where Y M and S are constants. Like in the previous functions,
;;; %MULTIPLY-HIGH is used when the intermediate values don't fit in a word.
;;; For signed words, the multiplier must be slightly changed when X is
;;; negative to produce the correct value, so a different multiplier is
;;; used depending on the sign of X.
;;; The 1+ at the end of ceiling is not added to the expression because the
;;; intermediate value can be used to calculate the remainder efficiently.
;;; To get the correct quotient, the 1+ has to be added after calling the
;;; function.
;;; It is possible that the function has to use an N+1 bit multiplier that
;;; doesn't fit in a word. When the args are unsigned words, this is handled
;;; as in the truncate code generator. Otherwise, the function returns NIL.
(flet ((gen (y min-x max-x choose-multiplier-fun large-y-expr min-quot max-quot)
  (declare (type (or (integer #.(- (expt 2 (1- sb!vm:n-word-bits))) -3)
                     (integer 3 #.most-positive-word)) y)
           (type (or sb!vm:signed-word word) min-x max-x))
  (aver (<= min-x max-x))
  (aver (not (zerop (logand y (1- y)))))
  (let* ((signed-p (or (minusp min-x) (minusp y)))
         (n-min (if signed-p (- (expt 2 (1- sb!vm:n-word-bits))) 0))
         (n-max (expt 2 (- sb!vm:n-word-bits (if signed-p 1 0))))
         (precision (integer-length (1- (max (abs min-x) (abs max-x)))))
         (mulhi (if signed-p '%signed-multiply-high '%multiply-high))
         (positive-product-p (if (plusp y) '(plusp x) '(minusp x)))
         (neg-m) (pos-m) (neg-shift) (pos-shift))
    (multiple-value-setq (neg-m neg-shift)
      (funcall choose-multiplier-fun (abs y) precision t))
    (multiple-value-setq (pos-m pos-shift)
      (funcall choose-multiplier-fun (abs y) precision nil))
    (when (and (>= (* y min-x) 0) (>= (* y max-x) 0))
      (setq neg-m pos-m)
      (setq neg-shift pos-shift))
    (when (and (<= (* y min-x) 0) (<= (* y max-x) 0))
      (setq pos-m neg-m)
      (setq pos-shift neg-shift))
    (let* ((shift `(if ,positive-product-p ,(- pos-shift) ,(- neg-shift)))
           (m `(if ,positive-product-p
                   ,(* (signum y) pos-m)
                   ,(* (signum y) neg-m)))
           (expr
            (cond
              ((> (abs y) (ash n-max -1))
               ;; When Y is above 2^(W-1), there are only a few
               ;; possible results, and we can use comparisons
               ;; to determine the correct one.
               large-y-expr)
              ((and (< (* max-x (max pos-m neg-m)) n-max)
                    (>= (* min-x (max pos-m neg-m)) n-min))
               `(ash (* x ,m) ,shift))
              (t
               (multiple-value-setq (pos-m pos-shift)
                 (get-scaled-multiplier pos-m pos-shift))
               (multiple-value-setq (neg-m neg-shift)
                 (get-scaled-multiplier neg-m neg-shift))
               (setq shift `(if ,positive-product-p ,(- pos-shift) ,(- neg-shift))
                     m `(if ,positive-product-p
                            ,(* (signum y) pos-m)
                            ,(* (signum y) neg-m)))
               (cond ((or (>= (max pos-m neg-m) n-max)
                          (< (min pos-m neg-m) n-min))
                      (if signed-p
                          nil
                          (flet ((word (x)
                                   `(truly-the word ,x)))
                            `(let* ((num x)
                                    (t1 (,mulhi num ,(- pos-m n-max))))
                               (ash ,(word `(+ t1 (ash ,(word `(- num t1))
                                                       -1)))
                                    ,(- 1 pos-shift))))))
                     ((and (zerop pos-shift) (zerop neg-shift))
                      `(,mulhi x ,m))
                     (t
                      `(ash (,mulhi x ,m)
                            ,shift)))))))
      (if expr
          `(truly-the (integer ,min-quot ,max-quot)
                      ,expr)
          nil)))))
  (defun gen-ceilinged-div-by-constant-expr (y min-x max-x)
    (let ((min (1- (ceiling min-x y)))
          (max (1- (ceiling max-x y))))
      (when (minusp y) (rotatef min max))
      (gen y min-x max-x 'choose-ceiling-multiplier
           (if (plusp y)
               `(cond ((> x ,y) 1)
                      ((>= x 0) 0)
                      ((> x ,(- y)) -1)
                      (t -2))
               `(cond ((< x ,y) 1)
                      ((<= x 0) 0)
                      ((< x ,(- y)) -1)
                      (t -2)))
         min max)))
  (defun gen-floored-div-by-constant-expr (y min-x max-x)
    (let ((min (floor min-x y))
          (max (floor max-x y)))
      (when (minusp y) (rotatef min max))
      (gen y min-x max-x 'choose-floor-multiplier
           (if (plusp y)
               `(cond ((>= x ,y) 1)
                      ((>= x 0) 0)
                      ((>= x ,(- y)) -1)
                      (t -2))
               `(cond ((<= x ,y) 1)
                      ((<= x 0) 0)
                      ((<= x ,(- y)) -1)
                      (t -2)))
         min max))))

;;; The following asserts show the expected average case and worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function for both signed and unsigned words, under a word size of 32 bits:
#+sb-xc-host
(when (= sb!vm:n-word-bits 32)
  ;; unsigned ceiling:
  (assert (equal
           (gen-ceilinged-div-by-constant-expr 7 0
                                               (1- (expt 2 sb!vm:n-word-bits)))
           '(truly-the (integer -1 613566756)
             (ash
              (%multiply-high x
               ;; The unnecessary condition checking is
               ;; removed at compile-time
               (if (plusp x)
                   1227133513
                   1227133513))
              (if (plusp x)
                  -1
                  -1)))))
  (assert (equal
           (gen-ceilinged-div-by-constant-expr 11 0
                                               (1- (expt 2 sb!vm:n-word-bits)))
           '(truly-the (integer -1 390451572)
             (let* ((num x) (t1 (%multiply-high num 1952257861)))
               (ash (truly-the word (+ t1 (ash (truly-the word (- num t1)) -1)))
                    -3)))))
  ;; signed ceiling:
  (assert (equal
           (gen-ceilinged-div-by-constant-expr 5
                                     (- (expt 2 (1- sb!vm:n-word-bits)))
                                     (1- (expt 2 (1- sb!vm:n-word-bits))))
           '(truly-the (integer -429496730 429496729)
             (ash
              (%signed-multiply-high x
               (if (plusp x)
                   858993459
                   1717986919))
              (if (plusp x)
                  0
                  -1)))))
  (assert (equal
           (gen-ceilinged-div-by-constant-expr 7
                                     (- (expt 2 (1- sb!vm:n-word-bits)))
                                     (1- (expt 2 (1- sb!vm:n-word-bits))))
           nil))
  ;; unsigned floor:
  (assert (equal
           (gen-floored-div-by-constant-expr 11 0
                                               (1- (expt 2 sb!vm:n-word-bits)))
           '(truly-the (integer 0 390451572)
             (ash
              (%multiply-high x
               ;; The unnecessary condition checking is
               ;; removed at compile-time
               (if (plusp x)
                   3123612579
                   3123612579))
              (if (plusp x)
                  -3
                  -3)))))
  (assert (equal
           (gen-floored-div-by-constant-expr 7 0
                                               (1- (expt 2 sb!vm:n-word-bits)))
           '(truly-the (integer 0 613566756)
             (let* ((num x) (t1 (%multiply-high num 613566757)))
               (ash (truly-the word (+ t1 (ash (truly-the word (- num t1)) -1)))
                    -2)))))
  ;; signed floor:
  (assert (equal
           (gen-floored-div-by-constant-expr 5
                                     (- (expt 2 (1- sb!vm:n-word-bits)))
                                     (1- (expt 2 (1- sb!vm:n-word-bits))))
           '(truly-the (integer -429496730 429496729)
             (ash
              (%signed-multiply-high x
               (if (plusp x)
                   1717986919
                   858993459))
              (if (plusp x)
                  -1
                  0)))))
  (assert (equal
           (gen-floored-div-by-constant-expr 7
                                     (- (expt 2 (1- sb!vm:n-word-bits)))
                                     (1- (expt 2 (1- sb!vm:n-word-bits))))
           nil)))

;;; If the divisor is constant and both args are positive and fit in a
;;; machine word, replace the division by a multiplication and possibly
;;; some shifts and an addition. Calculate the remainder by a second
;;; multiplication and a subtraction. Dead code elimination will
;;; suppress the latter part if only the quotient is needed.
(deftransform truncate ((x y) (word (constant-arg word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert unsigned integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     most-positive-word)))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand y (1- y)))
      (give-up-ir1-transform))
    `(let* ((quot ,(gen-unsigned-div-by-constant-expr y max-x
                                                      (<= max-x
                                                          most-positive-fixnum)))
            (rem (ldb (byte #.sb!vm:n-word-bits 0)
                      (- x (* quot ,y)))))
       (values quot rem))))

;;; Similar code for ceilinged division.
;;; Calculate the remainder with X-(Q-1)*Y-Y instead of X-Q*Y so
;;; that the values never overflow.
(deftransform ceiling ((x y) (word (constant-arg word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert unsigned integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     most-positive-word)))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand y (1- y)))
      (give-up-ir1-transform))
    `(if (zerop x)
         ;; the generated expression is only correct when X isn't 0
         ;; so we have to handle that case separately
         (values 0 0)
         (let* ((quot ,(gen-ceilinged-div-by-constant-expr y 0 max-x))
                (rem (truly-the (integer ,(- 1 y) 0)
                            (- (truly-the (integer 1 ,y)
                                          (- x
                                             (*
                                              (truly-the
                                               (integer 0 ,(1- (ceiling max-x y)))
                                               quot)
                                              ,y)))
                               ,y))))
           (values (1+ quot) rem)))))

;;; Similar to previous truncate transform, but with signed args.
(deftransform truncate ((x y) (sb!vm:signed-word
                               (constant-arg sb!vm:signed-word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert signed integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits)) 1)))
         (min-x  (or (and (numeric-type-p x-type)
                          (numeric-type-low x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits))))))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand (abs y) (1- (abs y))))
      (give-up-ir1-transform))
    ;; Use the unsigned transform instead, if we can.
    (unless (or (< y 0) (< min-x 0)) (give-up-ir1-transform))
    `(let* ((quot ,(gen-signed-div-by-constant-expr y min-x max-x
                                                    (and
                                                     (>= min-x
                                                         most-negative-fixnum)
                                                     (<= max-x
                                                         most-positive-fixnum))))
            (rem (truly-the (integer ,(- 1 (abs y)) ,(- (abs y) 1))
                            (- x (* quot ,y)))))
       (values quot rem))))

;;; Ceiling with signed args.
;;; Calculate the remainder either normally or as in the unsigned
;;; transform, depending on the sign of X. (Both methods may result
;;; in an overflow in the other case.)
(deftransform ceiling ((x y) (sb!vm:signed-word
                               (constant-arg sb!vm:signed-word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert signed integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits)) 1)))
         (min-x  (or (and (numeric-type-p x-type)
                          (numeric-type-low x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits))))))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand (abs y) (1- (abs y))))
      (give-up-ir1-transform))
    ;; Use the unsigned transform if we can since it has a
    ;; simpler remainder calculation
    (when (and (>= min-x 0) (<= max-x most-positive-word)
               (typep y 'word))
      (give-up-ir1-transform))
    (let ((quot-expr (gen-ceilinged-div-by-constant-expr y min-x max-x))
          (positive-p (if (plusp y) '(plusp x) '(minusp x)))
          (quot-min (ceiling min-x y))
          (quot-max (ceiling max-x y)))
      (unless quot-expr (give-up-ir1-transform))
      (when (minusp y) (rotatef quot-min quot-max))
      (when (plusp quot-min) (decf quot-min))
      (when (plusp quot-max) (decf quot-max))
      `(if (zerop x)
           ;; the generated expression is only correct when X isn't 0
           ;; so we have to handle that case separately
           (values 0 0)
           (let ((quot ,quot-expr))
             (unless ,positive-p (incf quot))
             (let ((rem (truly-the (integer ,(if (plusp y) (- 1 y) y)
                                            ,(if (plusp y) y (- -1 y)))
                                   (- x
                                      (* (truly-the (integer ,quot-min ,quot-max)
                                                    quot)
                                         ,y)))))
               (if ,positive-p
                   (values (1+ quot)
                           (truly-the (integer
                                       ,(if (plusp y) (- 1 y) 0)
                                       ,(if (plusp y) 0 (- -1 y)))
                                      (- rem ,y)))
                   (values quot rem))))))))

;;; Floor with signed args.
;;; Calculate the remainder by using X-(Q+1)*Y+Y when the result
;;; is negative and X-Q*Y otherwise, to avoid an overflow.
(deftransform floor ((x y) (sb!vm:signed-word
                               (constant-arg sb!vm:signed-word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert signed integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits)) 1)))
         (min-x  (or (and (numeric-type-p x-type)
                          (numeric-type-low x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits))))))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand (abs y) (1- (abs y))))
      (give-up-ir1-transform))
    ;; Use the unsigned transform if we can since it has a
    ;; simpler remainder calculation
    (when (and (>= min-x 0) (<= max-x most-positive-word)
               (typep y 'word))
      (give-up-ir1-transform))
    (let ((quot-expr (gen-floored-div-by-constant-expr y min-x max-x))
          (negative-p (if (plusp y) '(minusp x) '(plusp x)))
          (quot-min (floor min-x y))
          (quot-max (floor max-x y)))
      (unless quot-expr (give-up-ir1-transform))
      (when (minusp y) (rotatef quot-min quot-max))
      (when (minusp quot-min) (incf quot-min))
      (when (minusp quot-max) (incf quot-max))
      `(let ((quot ,quot-expr))
         (when ,negative-p (incf quot))
         (let ((rem (truly-the (integer ,(if (plusp y) (- y) (1+ y))
                                        ,(if (plusp y) (1- y) (- y)))
                               (- x
                                  (* (truly-the (integer ,quot-min ,quot-max)
                                                quot)
                                     ,y)))))
           (if ,negative-p
               (values (1- quot)
                       (truly-the (integer
                                   ,(if (plusp y) 0 (1+ y))
                                   ,(if (plusp y) (1- y) 0))
                                  (+ rem ,y)))
               (values quot rem)))))))
