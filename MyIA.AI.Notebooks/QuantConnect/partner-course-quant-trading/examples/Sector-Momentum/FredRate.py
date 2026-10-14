# region imports
from AlgorithmImports import *
# endregion

class FredRate(PythonData):
    """
    Source FRED DFF (Effective Federal Funds Rate).

    Piege classique du `PythonData` daté au jour de la ligne sans heure de fin :
    FRED publie la serie DFF du jour J vers 18:00 ET (release H.15). Si l'on
    borne la donnée uniquement par `Time = J 00:00` (defaut Lean : `EndTime =
    Time + 1 day`), la donnée est considere comme valide **toute la journee J**
    alors qu'elle n'est pas encore publiee avant 18:00 ET. Un algorithme qui
    decide pendant la seance de J (avant 18:00 ET) lit alors une valeur qui
    n'existait pas au moment de la decision : c'est le lookahead bias que le
    grain #19837 / #19825 denonce.

    Correctif : on serre `EndTime` a 18:00 ET du jour J, ce qui :
      - pour une decision placee AVANT 18:00 ET le jour J, l'algo ne voit PAS
        la valeur publiee (l'insight est absent -> la strategie ignore la
        feature et/ou utilise la veille via `History`) ;
      - pour une decision placee APRES 18:00 ET le jour J, l'algo voit la
        valeur du jour J correctement datee.

    Ce pattern est aussi documente pour les donnees alternatives (news,
    sentiment, macro releases) toutes publiees a une heure intraday non
    nulle. Voir la tranche 2 du grain #19837.
    """

    def GetSource(self, config, date, isLiveMode):
        return SubscriptionDataSource("https://fred.stlouisfed.org/graph/fredgraph.csv?id=DFF", SubscriptionTransportMedium.RemoteFile)

    def Reader(self, config, line, date, isLiveMode):
        data = line.split(',')
        if data[0] == 'DATE':
            return None
        rate = FredRate()
        rate.Symbol = config.Symbol
        rate.Time = datetime.strptime(data[0], "%Y-%m-%d")
        # EndTime explicite = 18:00 ET du jour J (FRED DFF publie a H.15 release).
        # Defaut Lean (Time + 1 day) surexpose la fenetre de validite et cree un
        # lookahead bias des qu'une alpha intraday lit la valeur le matin.
        rate.EndTime = rate.Time + timedelta(hours=18)
        rate.Value = float(data[1])
        return rate
