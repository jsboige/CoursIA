@echo off
setlocal
set CUDA_VISIBLE_DEVICES=2
set PYTHONUNBUFFERED=1

set PY=C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe
set TRAIN=%~dp0train_multiscale_gnn.py
set OUT=%~dp0..\results\m7_robustness_sweep
set OVERALL=%OUT%\_overall.log

echo [%date% %time%] START run1_ext_horizons >> "%OVERALL%"
"%PY%" "%TRAIN%" --horizons 1 2 3 4 5 7 10 14 21 28 --seeds 0 1 7 42 99 777 1024 2048 --n-splits 5 --epochs 1000 --coins BTC-USD ETH-USD --skip-remote --out-json "%OUT%\run1_ext_horizons.json" > "%OUT%\run1_ext_horizons.log" 2>&1
echo [%date% %time%] END   run1_ext_horizons exit=%ERRORLEVEL% >> "%OVERALL%"

echo [%date% %time%] START run2_more_splits >> "%OVERALL%"
"%PY%" "%TRAIN%" --horizons 1 3 5 10 20 30 --seeds 0 1 7 42 99 777 1024 2048 --n-splits 7 --epochs 1000 --coins BTC-USD ETH-USD --skip-remote --out-json "%OUT%\run2_more_splits.json" > "%OUT%\run2_more_splits.log" 2>&1
echo [%date% %time%] END   run2_more_splits exit=%ERRORLEVEL% >> "%OVERALL%"

echo [%date% %time%] START run3_more_seeds >> "%OVERALL%"
"%PY%" "%TRAIN%" --horizons 1 3 5 10 20 30 --seeds 0 1 7 11 13 17 19 42 99 777 1024 2048 --n-splits 5 --epochs 1000 --coins BTC-USD ETH-USD --skip-remote --out-json "%OUT%\run3_more_seeds.json" > "%OUT%\run3_more_seeds.log" 2>&1
echo [%date% %time%] END   run3_more_seeds exit=%ERRORLEVEL% >> "%OVERALL%"

echo [%date% %time%] START run4_longer_training >> "%OVERALL%"
"%PY%" "%TRAIN%" --horizons 1 3 5 10 20 30 --seeds 0 1 7 42 99 777 1024 2048 --n-splits 5 --epochs 2000 --coins BTC-USD ETH-USD --skip-remote --out-json "%OUT%\run4_longer_training.json" > "%OUT%\run4_longer_training.log" 2>&1
echo [%date% %time%] END   run4_longer_training exit=%ERRORLEVEL% >> "%OVERALL%"

echo [%date% %time%] ALL DONE >> "%OVERALL%"
endlocal
