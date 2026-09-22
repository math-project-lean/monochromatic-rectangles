# 격자점 색칠과 단색 직사각형의 최소 높이

양의 정수 $n$에 대해, 가로 $n+1$열·세로 $\ell$행의 정사각 격자점을 $n$가지 색으로 칠한다. 어떻게 칠하더라도 같은 색의 네 점을 꼭짓점으로 하는 직사각형이 반드시 생기게 하는 $\ell$의 최솟값을 구한다.

**직사각형은 기울어져 있어도 된다.** 가로·세로 격자 간격은 같고, 주어진 색을 모두 사용할 의무는 없다.

답은 다음과 같다.

$$
\boxed{\ell_{\min}=n\binom{n+1}{2}+1=\frac{n^2(n+1)}2+1}
$$

이 저장소에는 사람이 읽는 증명, 일반적인 모든 $n>0$에 대한 Lean 4 형식 증명, 유한 범위의 Python 검산 코드가 있다.

## 증명한 내용

비둘기집 원리로 위 높이에서 축에 평행한 단색 직사각형이 반드시 생김을 보인다. 최소성은 한 행 적은 격자에 대한 명시적 색칠을 구성하고, 축에 평행한 직사각형과 기울어진 직사각형을 모두 배제하여 증명한다.

최종 Lean 정리는 다음과 같다.

```lean
RectangleColoring.minimum_height (n : ℕ) (hn : 0 < n) :
  RectangleColoring.IsMinimum n (n ^ 2 * (n + 1) / 2 + 1)
```

`IsMinimum n l`은 높이 `l`의 모든 색칠에서 단색 직사각형이 생기고, 모든 `k < l`에 대해서는 이를 피하는 색칠이 존재한다는 뜻이다. `IsRectangle`은 정수 좌표의 평행사변형·직교·비퇴화 조건으로 정의하여 모든 방향의 직사각형을 포함한다.

증명에는 `sorry`, `admit`, 추가 공리, `native_decide`가 없다. 최종 정리의 공리 의존성은 Lean/Mathlib의 표준 공리인 `propext`, `Classical.choice`, `Quot.sound`뿐이다. Python 검산 결과는 Lean 증명의 전제로 사용하지 않는다.

## 읽을 파일

| 파일 | 내용 |
|---|---|
| [solution.pdf](solution.pdf) | 바로 읽거나 인쇄할 수 있는 한국어 PDF 풀이 |
| [solution.tex](solution.tex) | PDF 풀이의 XeLaTeX 원본 |
| [solution.md](solution.md) | 상한과 하한을 포함한 수학적 증명 |
| [Main.lean](lean/RectangleColoring/Main.lean) | 최종 최소값 정리 |
| [Basic.lean](lean/RectangleColoring/Basic.lean) | 격자·색칠·직사각형·최소값의 정의 |
| [Construction.lean](lean/RectangleColoring/Construction.lean) | 하한을 위한 명시적 색칠 |
| [verify.py](verify.py) | 유한 범위의 독립적인 검산 |
| [PROJECT_INDEX_FOR_AI.md](PROJECT_INDEX_FOR_AI.md) | 증명 모듈과 작업 재개 안내 |
| [SUMMARY_FOR_ME.md](SUMMARY_FOR_ME.md) | 짧은 요약 |

Lean 소스는 `lean/` 아래에 있으며, 진입 모듈을 포함하여 총 17개 파일이다.

## TeX와 PDF

`solution.tex`은 한국어를 지원하는 XeLaTeX로 컴파일한다. XeLaTeX, ko.TeX, `fontspec` 및 문서에 지정된 한글 글꼴 중 하나가 필요하다.

```sh
xelatex -interaction=nonstopmode -halt-on-error solution.tex
xelatex -interaction=nonstopmode -halt-on-error solution.tex
```

저장소에 완성된 `solution.pdf`도 포함하므로, 풀이를 읽을 때 직접 컴파일할 필요는 없다.

## Lean 검증

Lean 버전은 `leanprover/lean4:v4.30.0-rc2`, Mathlib은 커밋 `5450b53e5ddc75d46418fabb605edbf36bd0beb6`에 고정되어 있다. Lean 도구 관리자인 elan을 설치한 뒤, 이 저장소의 루트에서 실행한다.

```sh
lake update
lake exe cache get
lake build RectangleColoring
```

`lake build`만 실행해도 같은 대상을 검사한다. 의존 패키지와 생성된 빌드 파일은 `.lake/`에 저장된다.

최종 정리의 공리 의존성을 직접 출력하려면 빌드 후 다음 명령을 실행한다.

```sh
lake env lean lean/RectangleColoring/Main.lean
```

## Python 검산

별도 Python 패키지는 필요하지 않다. 저장소 루트에서 실행한다.

```sh
python verify.py --max-n 12
```

`12`를 바꾸면 검사 범위를 조절할 수 있다. 큰 값을 넣으면 실행 시간이 늘어난다. 유한 범위의 계산은 색칠 구성을 확인하는 보조 수단이며, 모든 $n>0$에 대한 결론은 Lean 정리로 증명되어 있다.
