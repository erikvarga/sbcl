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
;;; multiplying by a/y. Used in gen-(un)signed-div-by-constant-expr
;;; and gen-(un)signed-mul-by-frac-expr.
(defun choose-multiplier (a y max-x)
  (let* ((max-shift (+ (integer-length max-x) (integer-length y)))
         (scale (ash a max-shift))
         (low (floor scale y))
         (k (1- (ceiling (ash 1 max-shift) max-x)))
         (high (floor (+ scale k) y))
         (diff (logxor low high))
         (delta (1- (integer-length diff))))
    (values (ash high (- delta)) (- max-shift delta))))

;; Get the multiply and shift value for ceilinged and floored
;; multiplication by a/y.
;; Used in gen-ceilinged/floored-mul-by-frac-expr.
(flet ((scale-down (multiplier shift)
         (let ((scale (min shift
                           (integer-length
                            (1- (logand multiplier
                                        (- multiplier)))))))
           (values (ash multiplier (- scale))
                   (- shift scale)))))
  (macrolet ((choose (neg-low neg-high pos-low pos-high)
               `(let* ((a-abs (abs a))
                       (shift (+ precision (integer-length y)))
                       (mul-low (* (signum a)
                                   (if (minusp (* x-sign a))
                                       ,neg-low
                                       ,pos-low)))
                       (mul-high (* (signum a)
                                    (if (minusp (* x-sign a))
                                        ,neg-high
                                        ,pos-high)))
                       (shift-low shift)
                       (shift-high shift))
                  (multiple-value-setq (mul-low shift-low)
                    (scale-down mul-low shift-low))
                  (multiple-value-setq (mul-high shift-high)
                    (scale-down mul-high shift-high))
                  (if (< (abs mul-low) (abs mul-high))
                      (values mul-low shift-low)
                      (values mul-high shift-high)))))
    (defun choose-ceiling-multiplier (a y precision x-sign)
      (choose (1+ (floor (* a-abs (expt 2 shift)) y))
              (floor (* (expt 2 shift)
                        (/ (1+ (* a-abs (expt 2 precision)))
                           (* y (expt 2 precision)))))
              (ceiling (* (expt 2 shift)
                          (/ (1- (* a-abs (expt 2 precision)))
                             (* y (expt 2 precision)))))
              (1- (ceiling (* a-abs (expt 2 shift)) y))))
    (defun choose-floor-multiplier (a y precision x-sign)
      (choose (1+ (floor (* (expt 2 shift)
                            (/ (1- (* a-abs (expt 2 precision)))
                               (* y (expt 2 precision))))))
              (floor (* a-abs (expt 2 shift)) y)
              (ceiling (* a-abs (expt 2 shift)) y)
              (1- (ceiling (* (expt 2 shift)
                              (/ (1+ (* a-abs (expt 2 precision)))
                                 (* y (expt 2 precision))))))))))

;;; Get the scaled multiply and shift value that can be used with
;;; multiply-high. Used in all the div-by-mul code generators.
(defun get-scaled-multiplier (m shift)
  (let ((scale (max 0 (- sb!vm:n-word-bits shift))))
    (values (* m (ash 1 scale))
            (+ shift scale (- sb!vm:n-word-bits)))))

;;; Generate an expression that performs multiplication by M
;;; and right-shifting by SHIFT as efficiently as possible.
;;; When no efficient code sequence is found, return NIL.
;;; Used in most the div-by-mul code generators.
(defun gen-multiply-shift-expr (m shift min-x max-x signed-p)
  (multiple-value-bind (scaled-m scaled-shift)
      (get-scaled-multiplier m shift)
    (let* ((scaled-m-bits (integer-length scaled-m))
           (n (- sb!vm:n-word-bits (if signed-p 1 0)))
           (max-num (expt 2 n))
           (mulhi-fun (if signed-p
                          '%signed-multiply-high
                          '%multiply-high))
           (mulhi-shift-fun (if signed-p
                                '%signed-multiply-high-and-shift
                                '%multiply-high-and-shift))
           (mul-add-fun (if signed-p
                            '%signed-multiply-and-add-high
                            '%multiply-and-add)))
      (cond ((and (= scaled-m-bits (1+ n))
                  (>= (+ scaled-shift sb!vm:n-word-bits) (1+ n)))
             ;; Perform N+1-bit multiply-shift when
             ;; the multiplier and shift value is
             ;; large enough.
             (if signed-p
                 `(ash (truly-the
                        sb!vm:signed-word
                        ,(if (plusp scaled-m)
                             `(+ (%signed-multiply-high
                                  x ,(- scaled-m (* 2 max-num)))
                                 x)
                             `(- (%signed-multiply-high
                                  x ,(+ scaled-m (* 2 max-num)))
                                 x)))
                       ,(- scaled-shift))
                 (flet ((word (x)
                          `(truly-the word ,x)))
                   `(let ((t1 (%multiply-high x ,(- scaled-m max-num))))
                      (ash ,(word `(+ t1 (ash ,(word `(- x t1))
                                              -1)))
                           ,(- 1 scaled-shift))))))
            ((and (<= (integer-length m) n)
                  (< (* max-x m) max-num)
                  (>= (* min-x m) (- max-num)))
             ;; If everything fits in a word, we can
             ;; do the multiplication and shift directly.
             `(ash (* x ,m) ,(- shift)))
            ((> scaled-m-bits n)
             ;; If the multiplier used for multiply-high is too
             ;; large, try to generate a 2N-bit multiply-shift.
             (setq scaled-shift
                   (max shift
                        (+ sb!vm:n-word-bits
                           (max (integer-length min-x)
                                (integer-length max-x))
                           (if signed-p 1 0)))
                   scaled-m
                   (ash m (- scaled-shift shift)))
             (if (and (<= shift scaled-shift)
                      (<= (integer-length scaled-m) (+ sb!vm:n-word-bits n))
                      ;; Attempt signed version only if
                      ;; %SIGNED-MULTIPLY-AND-ADD-HIGH
                      ;; can be done efficiently.
                      #!-multiply-high-vops
                      (not signed-p))
                 (let ((shift-rem (- (* 2 sb!vm:n-word-bits) scaled-shift)))
                   (let ((m-high (* (signum scaled-m)
                                    (ash (abs scaled-m) (- sb!vm:n-word-bits))))
                         (m-low (* (signum scaled-m)
                                   (ldb (byte sb!vm:n-word-bits 0)
                                        (abs scaled-m)))))
                     (if (and (typep m-high 'sb!vm:signed-word)
                              (typep m-low 'sb!vm:signed-word))
                         `(let ((x (ash x ,shift-rem)))
                            ,(if (< (+ (max (integer-length (* min-x m-low))
                                            (integer-length (* max-x m-low)))
                                       shift-rem)
                                    sb!vm:n-word-bits)
                                 ;; There's no need to add the second
                                 ;; product if it's always 0.
                                 `(,mulhi-fun x ,m-high)
                                 `(values (,mul-add-fun x ,m-high
                                              (,mulhi-fun x ,m-low)))))
                         nil)))
                 nil))
            (t
             ;; Since the scaled multiplier fits into
             ;; a word, we can use multiply-high.
             `(,mulhi-shift-fun x ,scaled-m ,scaled-shift))))))

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
(defun gen-unsigned-div-by-constant-expr (y max-x)
  (declare (type (integer 3 #.most-positive-word) y)
           (type word max-x))
  (aver (not (zerop (logand y (1- y)))))
  (flet ((ld (x)
             ;; the floor of the binary logarithm of (positive) X
             (integer-length (1- x))))
    (let* ((n (expt 2 sb!vm:n-word-bits))
           (shift1 0))
      (multiple-value-bind (m shift2)
          (choose-multiplier 1 y max-x)
        (cond
          ((> y (truncate max-x 3))
           ;; When Y is large enough, it's faster to
           ;; determine the quotient with comparisons.
            `(cond ((< x ,y) 0)
                   ((< x ,(* y 2)) 1)
                   (t 2)))
          ((< (* max-x m) n)
           `(ash (* x ,m) ,(- shift2)))
          (t
           (multiple-value-setq (m shift2)
             (get-scaled-multiplier m shift2))
           (when (and (>= m n) (evenp y))
             (setq shift1 (ld (logand y (- y))))
             (multiple-value-setq (m shift2)
               (multiple-value-call 'get-scaled-multiplier
                 (choose-multiplier 1 (/ y (ash 1 shift1))
                                    (ash max-x (- shift1))))))
           (if (>= m n)
               (if (< max-x (1- n))
                   (let* ((shift
                           (+ (integer-length max-x) (integer-length y) -1))
                          (m (floor (ash 1 shift) y)))
                     (if (< (* (1+ max-x) m) n)
                         `(ash (* (+1 x) ,m) ,(- shift))
                         (let ((scale
                                (max 0 (- sb!vm:n-word-bits shift))))
                           `(ash (%multiply-high (1+ x)
                                                 ,(ash m scale))
                                 ,(- sb!vm:n-word-bits shift scale)))))
                   (flet ((word (x)
                            `(truly-the word ,x)))
                     `(let* ((num x)
                             (t1 (%multiply-high num ,(- m n))))
                        (ash ,(word `(+ t1 (ash ,(word `(- num t1))
                                                -1)))
                             ,(- 1 shift2)))))
               ;; Explicit TRULY-THE needed to get the FIXNUM=>FIXNUM
               ;; VOP
               `(truly-the (integer 0 ,(truncate max-x y))
                           (%multiply-high-and-shift
                            (logandc2 x ,(1- (ash 1 shift1)))
                            ,m
                            ,(+ shift1 shift2))))))))))

;;; The following two asserts show the expected average case and worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function, under a word size of 32 bits:
#+sb-xc-host
(when (= sb!vm:n-word-bits 32)
  (assert (equal (gen-unsigned-div-by-constant-expr 10 most-positive-word)
                 '(truly-the (integer 0 429496729)
                   (%multiply-high-and-shift (logandc2 x 0) 3435973837 3))))
  (assert (equal (gen-unsigned-div-by-constant-expr 7 most-positive-word)
                 '(let* ((num x)
                         (t1 (%multiply-high num 613566757)))
                   (ash
                    (truly-the word
                     (+ t1 (ash (truly-the word (- num t1)) -1)))
                    -2)))))

;;; Return an expression for calculating the quotient like in the previous
;;; function, but the arguments have to fit in signed words.
;;; The algorithm is taken from the same paper, Figure 5.2
(defun gen-signed-div-by-constant-expr (y min-x max-x)
  (declare (type (or (integer #.(- (expt 2 (1- sb!vm:n-word-bits))) -3)
                     (integer 3 #.(expt 2 (1- sb!vm:n-word-bits)))) y)
           (type sb!vm:signed-word min-x max-x))
  (aver (not (zerop (logand (abs y) (1- (abs y))))))
  (aver (<= min-x max-x))
  (when (> (abs y) (ash (max (abs max-x) (abs min-x)) -1))
    ;; When Y is large enough, it's faster to
    ;; determine the quotient with comparisons.
    (return-from gen-signed-div-by-constant-expr
      (if (plusp y)
          `(cond ((<= x ,(- y)) -1)
                 ((< x ,y) 0)
                 (t 1))
          `(cond ((<= x ,y) 1)
                 ((< x ,(- y)) 0)
                 (t -1)))))
  (let ((expr
         (multiple-value-bind (m shift)
             (choose-multiplier 1 (abs y) (max (abs max-x) (abs min-x)))
           ;; Determine the range of the quotient before
           ;; the negation and subtraction is applied to it
           (let ((max (truncate max-x (abs y)))
                 (min (1- (truncate min-x (abs y)))))
             `(truly-the (integer ,min ,max)
                         ,(gen-multiply-shift-expr
                           m shift min-x max-x t))))))
    (setq expr
          `(- ,expr (ash x ,(- sb!vm:n-word-bits))))
    (when (minusp y)
      (setq expr `(- ,expr)))
    (let ((max (truncate max-x y))
          (min (truncate min-x y)))
      (when (minusp y) (rotatef min max))
      `(truly-the (integer ,min ,max)
                  ,expr))))

;;; The following two asserts show the expected average case and worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function, under a word size of 32 bits:
#+sb-xc-host
(when (= sb!vm:n-word-bits 32)
  (macrolet ((gen (y)
               `(gen-signed-div-by-constant-expr
                 ,y
                 (- (expt 2 (1- sb!vm:n-word-bits)))
                 (1- (expt 2 (1- sb!vm:n-word-bits))))))
    (assert (equal
             (gen 11)
             '(truly-the (integer -195225786 195225786)
               (-
                (truly-the (integer -195225787 195225786)
                 (%signed-multiply-high-and-shift x 780903145 1))
                (ash x -32)))))
    (assert (equal
             (gen 7)
             '(truly-the (integer -306783378 306783378)
               (-
                (truly-the (integer -306783379 306783378)
                 (ash
                  (truly-the sb!vm:signed-word
                             (+ (%signed-multiply-high x -1840700269) x))
                  -2))
                (ash x -32)))))))

;;; Return an expression to calculate truncated multiplication of an
;;; integer by constant rational A/Y, using multiplication, shift and
;;; add/sub instead of division. The integer and the numerator/denominator
;;; of the rational arg must be positive and fit in a machine word.
(defun gen-unsigned-mul-by-frac-expr (a y max-x)
  (declare (type word a y max-x))
  (multiple-value-bind (m shift)
      (choose-multiplier a y max-x)
    (let ((s (expt 2 shift)))
      (when (> s (truncate (* m max-x) 3))
        ;; When the shift value is large enough, it's faster
        ;; to determine the quotient with comparisons.
        (return-from gen-unsigned-mul-by-frac-expr
          `(cond ((< x ,(ceiling s m)) 0)
                 ((< x ,(ceiling (* s 2) m)) 1)
                 (t 2)))))
    (let ((divisor 1)
          (m-bits (integer-length m)))
      (when (and (> m-bits (1+ sb!vm:n-word-bits)) (evenp y))
        (let ((scale (logand y (- y))))
          (when (< a scale)
            ;; When the Y is a multiple of 2^P, generate
            ;; a multiplication by A/2^P and a truncated
            ;; division by Y/2^P (The truncate is added
            ;; at the end).
            (setq divisor (/ y scale)
                  m a
                  m-bits (integer-length m)
                  shift (1- (integer-length scale))
                  y scale))))
      (let ((expr
             (gen-multiply-shift-expr m shift 0 max-x nil)))
        (unless expr
          (setq expr
                (if (> a y)
                    ;; If no multiply-shift code is available,
                    ;; and A/Y > 1, multiply with its integer part
                    ;; and the remainder separately.
                    (let ((q (truncate a y)))
                      `(+ (* x ,q)
                          ,(gen-unsigned-mul-by-frac-expr
                            (- a (* y q))
                            y max-x)))
                    ;; Otherwise, perform generic
                    ;; multiplication and shift.
                    `(ash (* x ,m) ,(- shift)))))
        `(values (truncate (truly-the (integer 0 ,(truncate (* max-x a) y))
                                      ,expr)
                           ,divisor))))))

;;; The following asserts show some of the average cases and the worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function, under a word size of 32 bits. The TRUNCATE is further optimized
;;; during compilation (transformed into multiply-shift or, in case of
;;; (TRUNCATE ... 1), removed altogether).
#+sb-xc-host
(when (= sb!vm:n-word-bits 32)
  (assert (equal (gen-unsigned-mul-by-frac-expr 3 7 most-positive-word)
                  '(values
                    (truncate
                     (truly-the (integer 0 1840700269)
                      (let ((t1 (%multiply-high x 3067833783)))
                        (ash
                         (truly-the word (+ t1 (ash
                                                (truly-the word (- x t1)) -1)))
                         -1)))
                     1))))
  (assert (equal (gen-unsigned-mul-by-frac-expr 7 24 most-positive-word)
                 '(values
                   (truncate
                    (truly-the (integer 0 3758096383)
                     (%multiply-high-and-shift x 3758096384 0))
                    3))))
  (assert (equal (gen-unsigned-mul-by-frac-expr 8 9 most-positive-word)
                 '(values
                   (truncate
                    (truly-the (integer 0 3817748706)
                     (ash (* x 30541989661) -35))
                    1)))))

;;; Return an expression for truncated mul-by-frac like in the previous
;;; function, but the arguments have to fit in signed words.
(defun gen-signed-mul-by-frac-expr (a y min-x max-x)
  (declare (type sb!vm:signed-word a min-x max-x)
           (type (integer 1 #.(1- (expt 2 (1- sb!vm:n-word-bits)))) y))
  (aver (<= min-x max-x))
  (multiple-value-bind (m shift)
      (choose-multiplier (abs a) y (max (abs max-x) (abs min-x)))
    (let ((s (expt 2 shift)))
      (when (and (>= (* min-x m) (* s -2)) (< (* max-x m) (* s 2)))
        ;; When the shift value is large enough, it's faster
        ;; to determine the quotient with comparisons.
        (return-from gen-signed-mul-by-frac-expr
          `(cond ((< x ,(ceiling (* s -1) m)) ,(- (signum a)))
                 ((< x ,(ceiling s m)) 0)
                 (t ,(signum a))))))
    (let ((max-product (truncate (* max-x a) y))
          (min-product (truncate (* min-x a) y))
          (expr (gen-multiply-shift-expr m shift min-x max-x t)))
      (when (minusp a) (rotatef min-product max-product))
      (unless expr
        (if (> (abs a) y)
            ;; If no multiply-shift code is available,
            ;; and ABS(A/Y) > 1, multiply with its
            ;; integer part and the remainder separately.
            (let ((q (truncate a y)))
              (return-from gen-signed-mul-by-frac-expr
                `(truly-the (integer ,min-product ,max-product)
                            (+ (* x ,q)
                               ,(gen-signed-mul-by-frac-expr
                                 (- a (* y q))
                                 y min-x max-x)))))
            ;; Otherwise, perform generic
            ;; multiplication and shift.
            (setq expr `(ash (* x ,m) ,(- shift)))))
      (let ((max (truncate (* max-x (abs a)) y))
            (min (1- (truncate (* min-x (abs a)) y))))
        (setq expr
              `(- (truly-the (integer ,min ,max) ,expr)
                  (ash x ,(- sb!vm:n-word-bits)))))
      (when (minusp a)
        (setq expr `(- ,expr)))
        `(truly-the (integer ,min-product ,max-product)
                    ,expr))))

;;; The following asserts show some of the average cases and the worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function, under a word size of 32 bits.
#+sb-xc-host
(when (= sb!vm:n-word-bits 32)
  (macrolet ((gen (a y)
               `(gen-signed-mul-by-frac-expr
                 ,a ,y
                 (- (expt 2 (1- sb!vm:n-word-bits)))
                 (1- (expt 2 (1- sb!vm:n-word-bits))))))
    (assert (equal (gen -2 3)
                   '(truly-the (integer -1431655764 1431655765)
                     (-
                      (-
                       (truly-the (integer -1431655766 1431655764)
                        (ash
                         (truly-the sb!vm:signed-word
                                    (+ (%signed-multiply-high x
                                                              -1431655765)
                                       x))
                         0))
                       (ash x -32))))))
    (assert (equal (gen 346 69)
                   '(truly-the (integer -10768541191 10768541186)
                     (+ (* x 5)
                      (truly-the (integer -31122951 31122951)
                       (-
                        (truly-the (integer -31122952 31122951)
                         (%signed-multiply-high-and-shift x
                                                          1991868891
                                                          5))
                        (ash x -32)))))))
    (assert (equal (gen 8 9)
                   '(truly-the (integer -1908874353 1908874352)
                     (-
                      (truly-the (integer -1908874354 1908874352)
                       (ash (* x 15270994831) -34))
                      (ash x -32)))))))

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
;;; doesn't fit in a word. This is handled similarly as in the truncate code
;;; generator.
(labels
    ((gen-core-expr (div-fun a y m shift min-x max-x signed-p
                     choose-multiplier-fun precision)
       (let ((divisor 1)
             (gen-fun (if (eq div-fun 'ceiling)
                          #'gen-ceiling
                          #'gen-floor))
             (m-bits (integer-length m))
             (scale (logand y (- y))))
         (when (and (eq div-fun 'floor)
                    (> m-bits (1+ sb!vm:n-word-bits)) (evenp y)
                    (< 1 (abs a) scale))
           ;; When the Y is a multiple of 2^P, generate
           ;; a multiplication by A/2^P and a
           ;; floored/ceilinged division by Y/2^P.
           ;; Only attempt when floored multiplication
           ;; is generated.
           (setq divisor (/ y scale)
                 y scale)
           (multiple-value-setq (m shift)
             (funcall choose-multiplier-fun a y precision
                      (+ (signum min-x)
                         (signum max-x))))
           (setq m-bits (integer-length m)))
         (let ((expr
                (gen-multiply-shift-expr m shift min-x max-x signed-p)))
           (unless expr
             (if (> (abs a) y)
                 ;; If no multiply-shift code is available,
                 ;; and ABS(A/Y) > 1, multiply with its
                 ;; integer part and the remainder separately.
                 (let ((q (truncate a y)))
                   (return-from gen-core-expr
                     `(+ (* x ,q)
                         ,(funcall gen-fun
                                   (- a (* y q))
                                   y min-x max-x))))
                 ;; Otherwise, perform generic
                 ;; multiplication and shift.
                 (setq expr `(ash (* x ,m) ,(- shift)))))
           (cond ((= 1 divisor) expr)
                 ;; Perform the division by Y/2^P.
                 (t
                  (setq min-x
                        (funcall div-fun
                                 (* min-x (/ a scale)))
                        max-x
                        (funcall div-fun
                                 (* max-x (/ a scale))))
                  (when (minusp a) (rotatef min-x max-x))
                  `(let ((x (truly-the (integer ,min-x ,max-x)
                                       (+ ,(if (eq div-fun 'ceiling) 1 0)
                                          ,expr))))
                     ,(funcall gen-fun
                               (signum divisor) (abs divisor)
                               min-x max-x)))))))
     (gen (div-fun a y min-x max-x min-res max-res)
       (declare (type (or sb!vm:signed-word word) a y min-x max-x))
       (aver (<= min-x max-x))
       (cond
         ((= 1 y) `(- (* x ,a) ,(if (eq div-fun 'ceiling) 1 0)))
         ((and (= (abs a) 1) (zerop (logand y (1- y))))
          ;; When the multiplicand is of the form 1/2^P, generate
          ;; a floored or ceilinged division by 2^P. This gets
          ;; transformed into faster operations later on.
          ;; Since the function must return one less than the
          ;; actual result of the ceilinged division, we subtract
          ;; one from the result in case of ceiling.
          `(truly-the (integer ,min-res ,max-res)
              (- (,div-fun x ,(* (signum a) y))
                 ,(if (eq div-fun 'ceiling) 1 0))))
         (t
          (let* ((choose-multiplier-fun
                  (if (eq div-fun 'ceiling)
                      'choose-ceiling-multiplier
                      'choose-floor-multiplier))
                 (signed-p (or (minusp min-x) (minusp a)))
                 (precision (integer-length
                             (1- (max (abs min-x)
                                      (abs max-x)))))
                 (neg-m) (pos-m) (neg-shift) (pos-shift))
            (multiple-value-setq (neg-m neg-shift)
              (funcall choose-multiplier-fun a y precision -1))
            (multiple-value-setq (pos-m pos-shift)
              (funcall choose-multiplier-fun a y precision 1))
            (let ((neg-expr (gen-core-expr
                             div-fun a y neg-m neg-shift min-x 0 signed-p
                             choose-multiplier-fun precision))
                  (pos-expr (gen-core-expr
                             div-fun a y pos-m pos-shift 0 max-x signed-p
                             choose-multiplier-fun precision)))
              `(truly-the (integer ,min-res ,max-res)
                  ,(cond ((<= max-x 0) neg-expr)
                         ((>= min-x 0) pos-expr)
                         (t `(if (plusp x) ,pos-expr ,neg-expr)))))))))
     (gen-ceiling (a y min-x max-x)
       (aver (plusp y))
       (let ((min (1- (ceiling (* a min-x) y)))
             (max (1- (ceiling (* a max-x) y))))
         (when (minusp a) (rotatef min max))
         (unless (or (minusp a) (minusp min-x))
           (setq min (max 0 min)))
         (let ((comp-limit (/ (* 2 y) a)))
           ;; When A/Y is small enough, there are only a few
           ;; possible results, and we can use comparisons
           ;; to determine the correct one.
           (if (if (plusp a)
                   (and (< max-x comp-limit)
                        (>= min-x (- comp-limit)))
                   (and (<= max-x (- comp-limit))
                        (> min-x comp-limit)))
               `(truly-the (integer ,min ,max)
                   ,(if (plusp a)
                        `(cond ((<= x ,(ceiling (- y) a)) -2)
                               ((<= x 0) -1)
                               ((<= x ,(ceiling y a)) 0)
                               (t 1))
                        `(cond ((< x ,(ceiling y a)) 1)
                               ((< x 0) 0)
                               ((< x ,(ceiling (- y) a)) -1)
                               (t -2))))
               (gen 'ceiling a y min-x max-x min max)))))
     (gen-floor (a y min-x max-x)
       (aver (plusp y))
       (let ((min (floor (* a min-x) y))
             (max (floor (* a max-x) y)))
         (when (minusp a) (rotatef min max))
         (let ((comp-limit (/ (* 2 y) a)))
           ;; When A/Y is small enough, there are only a few
           ;; possible results, and we can use comparisons
           ;; to determine the correct one.
           (if (if (plusp a)
                 (and (< max-x comp-limit)
                      (>= min-x (- comp-limit)))
                 (and (<= max-x (- comp-limit))
                      (> min-x comp-limit)))
               `(truly-the (integer ,min ,max)
                   ,(if (plusp a)
                        `(cond ((< x ,(ceiling (- y) a)) -2)
                               ((< x 0) -1)
                               ((< x ,(ceiling y a)) 0)
                               (t 1))
                        `(cond ((<= x ,(ceiling y a)) 1)
                               ((<= x 0) 0)
                               ((<= x ,(ceiling (- y) a)) -1)
                               (t -2))))
               (gen 'floor a y min-x max-x min max))))))
  (defun gen-ceilinged-mul-by-frac-expr (a y min-x max-x)
    (gen-ceiling a y min-x max-x))
  (defun gen-floored-mul-by-frac-expr (a y min-x max-x)
    (gen-floor a y min-x max-x)))

;;; The following asserts show the expected average case and worst case
;;; with respect to the complexity of the generated expression of the previous
;;; function for both signed and unsigned words, under a word size of 32 bits:
#+sb-xc-host
(when (= sb!vm:n-word-bits 32)
  (macrolet ((gen (y div-type sign-type)
               `(,(if (eq div-type 'ceiling)
                      'gen-ceilinged-mul-by-frac-expr
                      'gen-floored-mul-by-frac-expr)
                  ,(signum y)
                  ,(abs y)
                  ,@(if (eq sign-type 'unsigned)
                        `(0 ,(1- (expt 2 sb!vm:n-word-bits)))
                        `(,(- (expt 2 (1- sb!vm:n-word-bits)))
                           ,(1- (expt 2 (1- sb!vm:n-word-bits))))))))
    ;; unsigned ceiling:
    (assert (equal
             (gen 7 ceiling unsigned)
             '(truly-the (integer 0 613566756)
               (%multiply-high-and-shift x 1227133513 1))))
    (assert (equal
             (gen 11 ceiling unsigned)
             '(truly-the (integer 0 390451572)
               (let ((t1 (%multiply-high x 1952257861)))
                 (ash
                  (truly-the word
                     (+ t1 (ash (truly-the word (- x t1)) -1)))
                  -3)))))
    ;; signed ceiling:
    (assert (equal
             (gen 5 ceiling signed)
             '(truly-the (integer -429496730 429496729)
               (if (plusp x)
                   (%signed-multiply-high-and-shift x 858993459 0)
                   (%signed-multiply-high-and-shift x 1717986919 1)))))
    (assert (equal
             (gen 7 ceiling signed)
             '(truly-the (integer -306783379 306783378)
               (if (plusp x)
                   (%signed-multiply-high-and-shift x 1227133513 1)
                   (ash
                    (truly-the sb!vm:signed-word
                      (+ (%signed-multiply-high x -1840700269) x))
                    -2)))))
    ;; unsigned floor:
    (assert (equal
             (gen 11 floor unsigned)
             '(truly-the (integer 0 390451572)
               (%multiply-high-and-shift x 3123612579 3))))
    (assert (equal
             (gen 7 floor unsigned)
             '(truly-the (integer 0 613566756)
               (let ((t1 (%multiply-high x 613566757)))
                 (ash
                  (truly-the word
                     (+ t1 (ash (truly-the word (- x t1)) -1)))
                  -2)))))
    ;; signed floor:
    (assert (equal
             (gen 5 floor signed)
             '(truly-the (integer -429496730 429496729)
               (if (plusp x)
                   (%signed-multiply-high-and-shift x 1717986919 1)
                   (%signed-multiply-high-and-shift x 858993459 0)))))
    (assert (equal
             (gen 7 floor signed)
             '(truly-the (integer -306783379 306783378)
               (if (plusp x)
                   (ash
                    (truly-the sb!vm:signed-word
                      (+ (%signed-multiply-high x -1840700269) x))
                    -2)
                   (%signed-multiply-high-and-shift x 1227133513 1)))))))

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
    `(let* ((quot ,(gen-unsigned-div-by-constant-expr y max-x))
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
         (let* ((quot ,(gen-ceilinged-mul-by-frac-expr
                        (signum y) (abs y) 0 max-x))
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
    `(let* ((quot ,(gen-signed-div-by-constant-expr y min-x max-x))
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
    (let ((quot-expr (gen-ceilinged-mul-by-frac-expr
                      (signum y) (abs y) min-x max-x))
          (positive-p (if (plusp y) '(plusp x) '(minusp x)))
          (quot-min (ceiling min-x y))
          (quot-max (ceiling max-x y)))
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
    ;; Attempt to use this transform causes an error during
    ;; compilation for some reason
    #+sb-xc-host (give-up-ir1-transform)
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand (abs y) (1- (abs y))))
      (give-up-ir1-transform))
    ;; Use the unsigned transform if we can since it has a
    ;; simpler remainder calculation
    (when (and (>= min-x 0) (<= max-x most-positive-word)
               (typep y 'word))
      (give-up-ir1-transform))
    (let ((quot-expr (gen-floored-mul-by-frac-expr
                      (signum y) (abs y) min-x max-x))
          (negative-p (if (plusp y) '(minusp x) '(plusp x)))
          (quot-min (floor min-x y))
          (quot-max (floor max-x y)))
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

;;; Replace truncated division of an integer by a constant rational with
;;; a sequence of multiplications, additions and shifts. The numerator,
;;; denominator and dividend has to be positive and fit in a machine word.
;;; Since the remainder is calculated by multiplying with a rational, this
;;; transform improves the performance only if the remainder is not needed.
(deftransform truncate ((x y) (word (constant-arg ratio))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert unsigned integer - rational division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (num (numerator y))
         (denom (denominator y))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     most-positive-word)))
    (unless (and (typep num 'word) (typep denom 'word))
      (give-up-ir1-transform))
    `(let* ((quot ,(gen-unsigned-mul-by-frac-expr denom num max-x))
            (rem (- x (* quot ,y))))
       (values quot rem))))
;;; Similar to previous truncate transform, but with signed args.
(deftransform truncate ((x y) (sb!vm:signed-word (constant-arg ratio))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert signed integer - rational division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (num (abs (numerator y)))
         (denom (* (signum y) (abs (denominator y))))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits)) 1)))
         (min-x  (or (and (numeric-type-p x-type)
                          (numeric-type-low x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits))))))
    (unless (and (typep num 'sb!vm:signed-word)
                 (typep denom 'sb!vm:signed-word))
      (give-up-ir1-transform))
    ;; Use the unsigned transform instead, if we can.
    (unless (or (< y 0) (< min-x 0)) (give-up-ir1-transform))
    `(let* ((quot ,(gen-signed-mul-by-frac-expr denom num min-x max-x))
            (rem (- x (* quot ,y))))
       (values quot rem))))

;; Ceilinged/floored division by rationals.
(macrolet
    ((def (ceiling-p signed-p)
       (let ((word-type (if signed-p
                            'sb!vm:signed-word
                            'word))
             (gen-fun (if ceiling-p
                          'gen-ceilinged-mul-by-frac-expr
                          'gen-floored-mul-by-frac-expr)))
         `(deftransform ,(if ceiling-p 'ceiling 'floor)
              ((x y) (,word-type (constant-arg ratio))
               *
               :policy (and (> speed compilation-speed)
                            (> speed space)))
            ,(format nil
                     "convert ~a integer - rational division to multiplication"
                     (if signed-p "signed" "unsigned"))
            (let* ((y      (lvar-value y))
                   (x-type (lvar-type x))
                   (num (abs (numerator y)))
                   (denom (* (signum y) (abs (denominator y))))
                   (max-x  (or (and (numeric-type-p x-type)
                                    (numeric-type-high x-type))
                               ,(if signed-p
                                    '(- (expt 2 (1- sb!vm:n-word-bits)) 1)
                                    'most-positive-word)))
                   (min-x  (or (and (numeric-type-p x-type)
                                    (numeric-type-low x-type))
                               ,(if signed-p
                                    '(- (expt 2 (1- sb!vm:n-word-bits)))
                                    0))))
              (unless (and (typep num ',word-type)
                           (typep denom ',word-type))
                (give-up-ir1-transform))
              `(if ,,(if ceiling-p ''(zerop x) ''nil)
                   ;; X = 0 has to be handled separately
                   ;; in ceiling.
                   (values 0 0)
                   (let* ((quot
                           (+ ,,(if ceiling-p 1 0)
                              ,(,gen-fun denom num min-x max-x)))
                          (rem (- x (* quot ,y))))
                     (values quot rem))))))))
  ;; Unsigned floor is already covered in unsigned truncate.
  (def t nil)
  (def nil t)
  (def t t))
