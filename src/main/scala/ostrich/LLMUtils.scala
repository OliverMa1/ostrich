package ostrich

import java.util.concurrent.TimeUnit

import org.json4s._
import org.json4s.native.JsonMethods._

import org.apache.commons.text.StringEscapeUtils

/*
Utility to do API calls to OLLAMA for now. I will keep everything constant can (should) be adapted later on.
 */
class LLMUtils {

  import okhttp3._


  val client : OkHttpClient = new OkHttpClient.Builder()
    .connectTimeout(60, TimeUnit.SECONDS)
    .readTimeout(300, TimeUnit.SECONDS)
    .writeTimeout(60, TimeUnit.SECONDS)
    .build()


  def generatePrompt(cutTrace : String): String = {

    val prompt = new StringBuilder()

    prompt.append(cutTrace)
    prompt.append("""\nYou are a helper oracle for the SMT string solver. The solver has decided to cut. This means to chose a variable
                    |and a string to cut on. The cut will be checked with the positive and negative assignment in parallel.
                    |Hence, a cut is good if it leads to a satisfying assignment as fast as possible or to a conflict as soon as possible in case of unsat.\n
                    |
                    |Your task is to  to chose a variable from the SMT problem above and decide on a string asignment for this exact variable.
                    |Do not provide anything else. I am only interested in the variable and the assignment, no explanation or any other text, only the variable and string.\n
                    |
                    |Chose one of the variables in the available cut variables and come up with a corresponding assignment!
                    |Return two lines, in the first line the name of the variable to cut on, and in the second line the string in quotations ("). """.stripMargin)

    prompt.toString()
  }

  def promptLLM(prompt: String) : String = {
    val escaped = StringEscapeUtils.escapeJson(prompt)
    val json =
      s"""{
      "model": "llama3.1:8b",
      "prompt": "$escaped",
      "stream": false
    }"""

    val body = RequestBody.create(
      MediaType.parse("application/json"),
      json
    )

    val request = new Request.Builder()
      .url("http://localhost:11434/api/generate")
      .post(body)
      .build()

    val response = client.newCall(request).execute()
    val res : String = response.body().string()

    extract(res)
  }

  def extract(json: String): String = {
    implicit val formats: DefaultFormats.type = DefaultFormats

    val parsed = parse(json)

    (parsed \ "response").extract[String]
  }

}
